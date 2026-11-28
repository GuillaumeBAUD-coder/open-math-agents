import Mathlib

/-!
# OEIS A287724: the n-th 1 of the {0->1, 1->010}-transform of the Fibonacci word stays near n * r

Source: https://oeis.org/A287724 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code, submitted by @SSmurf.

Entry (Clark Kimberling, Jun 02 2017), offset 1: Positions of 1 in A287722; complement of A287723.
Comment: Conjecture: 0 < n*r - a(n) < 3 for n >= 1, where r = 4 - sqrt(5).
A287722 is the {0->1, 1->010}-transform of the infinite Fibonacci word A003849.

Formalization notes:
* Words are lists of the digits 0 and 1. `fibSigma` is the Fibonacci morphism 0 -> 01, 1 -> 0
  and `fib k` is its k-th iterate applied to the word 0; each iterate extends the one before, and
  their limit is the infinite Fibonacci word A003849 = 0, 1, 0, 0, 1, 0, 1, 0, ...
* `phi` is the transform: every 0 is replaced by 1 and every 1 by 010.
* `A287722 i` is the i-th letter (i >= 1) of the transformed word, read off the image of `fib i`,
  which has more than i letters; any later iterate gives the same letter (the word starts
  1, 0, 1, 0, 1, 1, 0, 1, as the data of A287722).
* `a n` is the n-th (n >= 1) position i >= 1 with A287722(i) = 1, counted from 1 as in the
  entry: `Nat.nth` of that set of positions at index n - 1. The first terms are
  a(1..8) = 1, 3, 5, 6, 8, 10, 12, 14, the entry's data.
* `main` states both strict inequalities in the reals, with `Real.sqrt`, for every n >= 1, with
  r = 4 - sqrt(5) as in the entry.
-/

namespace OMA.S_oeis_a287724

/-- The Fibonacci morphism 0 -> 01, 1 -> 0 (only the letters 0 and 1 occur). -/
def fibSigma : ℕ → List ℕ
  | 0 => [0, 1]
  | _ => [0]

/-- The k-th iterate of the Fibonacci morphism applied to the word 0. -/
def fib (k : ℕ) : List ℕ := (fun w : List ℕ => w.flatMap fibSigma)^[k] [0]

/-- The transform 0 -> 1, 1 -> 010. -/
def phi : ℕ → List ℕ
  | 0 => [1]
  | _ => [0, 1, 0]

/-- A287722(i) for i >= 1: the i-th letter of the transformed Fibonacci word. -/
def A287722 (i : ℕ) : ℕ := ((fib i).flatMap phi).getD (i - 1) 0

/-- A287724(n) for n >= 1: the position of the n-th 1 in A287722. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => 1 ≤ i ∧ A287722 i = 1) (n - 1)

/-- Kimberling's conjecture. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    0 < (n : ℝ) * (4 - Real.sqrt 5) - a n ∧
      (n : ℝ) * (4 - Real.sqrt 5) - a n < 3 := by
  sorry

end OMA.S_oeis_a287724
