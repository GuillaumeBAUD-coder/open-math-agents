import Mathlib

/-!
# OEIS A285597: positions of 0 in the 0-limiting word of 0 -> 11, 1 -> 0111

Source: https://oeis.org/A285597 (OEIS Foundation, CC BY-SA 4.0).

Entry (Clark Kimberling), offset 1: Positions of 0 in A285596; complement of A285598. Comment: Conjecture: a(n)/n -> (5+sqrt(17))/2.
A285596 is the 0-limiting word of the morphism 0 -> 11, 1 -> 0111.

Formalization notes:
* Words are lists of the digits 0 and 1 and `sigma` is the morphism.
* `iter k` applies the morphism 2k times to the word 0: the 0-limiting word is the
  fixed point beginning with 0 of the square of the morphism, which is the limit of these
  iterates (each extends the one before).
* `A285596 i` is the i-th letter (i >= 1) of the word, read off `iter i`, which has more than
  i letters; any later iterate gives the same letter.
* `a n` is the n-th (n >= 1) position i >= 1 with A285596(i) = 0, counted from 1 as in the
  entry: `Nat.nth` of that set of positions at index n - 1.
* `main` states the limit of a(n)/n in the reals, with `Real.sqrt`.
* Data check: a(1..8) = 1, 5, 11, 15, 19, 25, 29, 33, the entry's data.
-/

namespace OMA.S_oeis_a285597

/-- The morphism 0 -> 11, 1 -> 0111 (only the letters 0 and 1 occur). -/
def sigma : ℕ → List ℕ
  | 0 => [1, 1]
  | _ => [0, 1, 1, 1]

/-- The (2k)-th iterate of the morphism applied to the word 0. -/
def iter (k : ℕ) : List ℕ :=
  (fun w : List ℕ => (w.flatMap sigma).flatMap sigma)^[k] [0]

/-- A285596(i) for i >= 1: the i-th letter of the word, read off `iter i`. -/
def A285596 (i : ℕ) : ℕ := (iter i).getD (i - 1) 0

/-- A285597(n) for n >= 1: the position of the n-th 0 in A285596. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => 1 ≤ i ∧ A285596 i = 0) (n - 1)

/-- Kimberling's conjecture. -/
theorem main : Filter.Tendsto (fun n : ℕ => (a n : ℝ) / n) Filter.atTop
    (nhds ((5 + Real.sqrt 17) / 2)) := by
  sorry

end OMA.S_oeis_a285597
