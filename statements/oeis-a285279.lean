import Mathlib

/-!
# OEIS A285279: the n-th 1 of the 1-limiting word of 0 -> 10, 1 -> 0111: the conjectured bounds on n * r - a(n)

Source: https://oeis.org/A285279 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code, submitted by @SSmurf.

Entry (Clark Kimberling, Apr 25 2017), offset 1: Positions of 1 in A285277; complement of A285278.
Comment: Conjecture: 0 < n*r - a(n) < 6 for n>=1, where r = 2+sqrt(2).
A285277 is the 1-limiting word of the morphism 0 -> 10, 1 -> 0111.

Formalization notes:
* Words are lists of the digits 0 and 1 and `sigma` is the morphism.
* `iter k` is the k-th iterate of the morphism applied to the word 0:
  0 -> 10 -> 011110 -> 10011101110111011110 -> ...
  The iterates with an even number of steps start with 0 and each extends the previous even one;
  those with an odd number of steps start with 1 and each extends the previous odd one. As in the
  comment of A285277, the 1-limiting word is the limit of the iterates with an odd number of
  steps (it starts 1, 0, 0, 1, 1, 1, 0, 1, as the data of A285277).
* `A285277 i` is the i-th letter (i >= 1) of that word, read off `iter (2 * i + 1)`, which has more
  than i letters; any later iterate of the same parity gives the same letter.
* `a n` is the n-th (n >= 1) position i >= 1 with A285277(i) = 1, counted from 1 as in the
  entry: `Nat.nth` of that set of positions at index n - 1. The first terms are
  a(1..8) = 1, 4, 5, 6, 8, 9, 10, 12, the entry's data.
* `main` states both strict inequalities in the reals, with `Real.sqrt`, for every n >= 1, with
  r = 2+sqrt(2) as in the entry.
* As written, the inequality already fails at n = 4: a(4) = 6 and
  4*r - a(4) = 7.6569, above the upper bound 6. `main` is the entry's literal text, so it
  is expected to be refuted, not proved.
-/

namespace OMA.S_oeis_a285279

/-- The morphism 0 -> 10, 1 -> 0111 (only the letters 0 and 1 occur). -/
def sigma : ℕ → List ℕ
  | 0 => [1, 0]
  | _ => [0, 1, 1, 1]

/-- The k-th iterate of the morphism applied to the word 0. -/
def iter (k : ℕ) : List ℕ := (fun w : List ℕ => w.flatMap sigma)^[k] [0]

/-- A285277(i) for i >= 1: the i-th letter of the 1-limiting word, read off `iter (2 * i + 1)`. -/
def A285277 (i : ℕ) : ℕ := (iter (2 * i + 1)).getD (i - 1) 0

/-- A285279(n) for n >= 1: the position of the n-th 1 in A285277. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => 1 ≤ i ∧ A285277 i = 1) (n - 1)

/-- Kimberling's conjecture. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    0 < (n : ℝ) * (2 + Real.sqrt 2) - a n ∧
      (n : ℝ) * (2 + Real.sqrt 2) - a n < 6 := by
  sorry

end OMA.S_oeis_a285279
