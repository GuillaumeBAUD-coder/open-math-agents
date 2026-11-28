import Mathlib

/-!
# OEIS A285658: positions of 0 in the fixed point of 0 -> 11, 1 -> 1011

Source: https://oeis.org/A285658 (OEIS Foundation, CC BY-SA 4.0).

Entry (Clark Kimberling), offset 1: Positions of 0 in A285657; complement of A285659. Comment: Conjecture: a(n)/n -> (5 + sqrt(17))/2.
A285657 is the fixed point of the morphism 0 -> 11, 1 -> 1011.

Formalization notes:
* Words are lists of the digits 0 and 1 and `sigma` is the morphism.
* `iter k` is the k-th iterate of the morphism applied to the word 1. The image of 1
  starts with 1, so each iterate extends the one before and their limit is the fixed point.
* `A285657 i` is the i-th letter (i >= 1) of the word, read off `iter i`, which has more than
  i letters; any later iterate gives the same letter.
* `a n` is the n-th (n >= 1) position i >= 1 with A285657(i) = 0, counted from 1 as in the
  entry: `Nat.nth` of that set of positions at index n - 1.
* `main` states the limit of a(n)/n in the reals, with `Real.sqrt`.
* Data check: a(1..8) = 2, 8, 12, 16, 20, 24, 30, 34, the entry's data.
-/

namespace OMA.S_oeis_a285658

/-- The morphism 0 -> 11, 1 -> 1011 (only the letters 0 and 1 occur). -/
def sigma : ℕ → List ℕ
  | 0 => [1, 1]
  | _ => [1, 0, 1, 1]

/-- The k-th iterate of the morphism applied to the word 1. -/
def iter (k : ℕ) : List ℕ :=
  (fun w : List ℕ => w.flatMap sigma)^[k] [1]

/-- A285657(i) for i >= 1: the i-th letter of the word, read off `iter i`. -/
def A285657 (i : ℕ) : ℕ := (iter i).getD (i - 1) 0

/-- A285658(n) for n >= 1: the position of the n-th 0 in A285657. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => 1 ≤ i ∧ A285657 i = 0) (n - 1)

/-- Kimberling's conjecture. -/
theorem main : Filter.Tendsto (fun n : ℕ => (a n : ℝ) / n) Filter.atTop
    (nhds ((5 + Real.sqrt 17) / 2)) := by
  sorry

end OMA.S_oeis_a285658
