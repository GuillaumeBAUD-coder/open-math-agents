import Mathlib

/-!
# OEIS A284955: positions of 0 in the 0-limiting word of 0 -> 10, 1 -> 000

Source: https://oeis.org/A284955 (OEIS Foundation, CC BY-SA 4.0).

Entry (Clark Kimberling), offset 1: Positions of 0 in A284954; complement of A284956.. Comment: Conjecture: a(n)/n -> (5 + sqrt(13))/6.
A284954 is the 0-limiting word of the morphism 0 -> 10, 1 -> 000.

Formalization notes:
* Words are lists of the digits 0 and 1 and `sigma` is the morphism.
* `iter k` applies the morphism 2k times to the word 0: the 0-limiting word is the
  fixed point beginning with 0 of the square of the morphism, which is the limit of these
  iterates (each extends the one before).
* `A284954 i` is the i-th letter (i >= 1) of the word, read off `iter i`, which has more than
  i letters; any later iterate gives the same letter.
* `a n` is the n-th (n >= 1) position i >= 1 with A284954(i) = 0, counted from 1 as in the
  entry: `Nat.nth` of that set of positions at index n - 1.
* `main` states the limit of a(n)/n in the reals, with `Real.sqrt`.
* Data check: a(1..8) = 1, 2, 3, 5, 6, 7, 8, 10, the entry's data.
-/

namespace OMA.S_oeis_a284955

/-- The morphism 0 -> 10, 1 -> 000 (only the letters 0 and 1 occur). -/
def sigma : ℕ → List ℕ
  | 0 => [1, 0]
  | _ => [0, 0, 0]

/-- The (2k)-th iterate of the morphism applied to the word 0. -/
def iter (k : ℕ) : List ℕ :=
  (fun w : List ℕ => (w.flatMap sigma).flatMap sigma)^[k] [0]

/-- A284954(i) for i >= 1: the i-th letter of the word, read off `iter i`. -/
def A284954 (i : ℕ) : ℕ := (iter i).getD (i - 1) 0

/-- A284955(n) for n >= 1: the position of the n-th 0 in A284954. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => 1 ≤ i ∧ A284954 i = 0) (n - 1)

/-- Kimberling's conjecture. -/
theorem main : Filter.Tendsto (fun n : ℕ => (a n : ℝ) / n) Filter.atTop
    (nhds ((5 + Real.sqrt 13) / 6)) := by
  sorry

end OMA.S_oeis_a284955
