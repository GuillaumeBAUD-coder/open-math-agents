import Mathlib

/-!
# OEIS A285682: a(n) - a(n-1) is in {5, 7}

Source: https://oeis.org/A285682 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, May 11 2017), offset 1: Positions of 1 in A285680.
Comment: A 3-way partition of the positive integers, by positions of 0, 1, 2 in A285680:
A285681: positions of 0; slope t = (15+sqrt(5))/10; A285682: positions of 1; slope u = 4+sqrt(5);
A285683: positions of 2; slope v = (1+3*sqrt(5))/2; where 1/t + 1/u + 1/v = 1. Conjecture:
a(n) - a(n-1) is in {5,7} for n >= 2. Data: 2, 7, 14, 19, 26, 33, 38, 45, ...
A285680 (Clark Kimberling, May 11 2017): {1010->2}-transform of the infinite Fibonacci word
A003849. Its program: w1 = StringReplace[w, {1010 -> 2}] with w the Fibonacci word.
A003849 (offset 0): The infinite Fibonacci word (start with 0, apply 0->01, 1->0, take limit).

Formalization notes:
* `sig` is the morphism 0 -> 01, 1 -> 0 on finite words and `fib n` is its n-th iterate on the
  word 0. Each iterate is a prefix of the next and iterate n has at least n + 1 letters (lemmas
  `fib_prefix` and `fib_length` of the proof), so `fw i`, letter i of iterate i + 1, is letter i
  of the limit word: `fw` is A003849 with its offset 0.
* The transform is StringReplace with the single rule 1010 -> 2 applied to the infinite word fw:
  read from the left, at each position a 1010 starting there is replaced by 2 and skipped, any
  other letter is copied. `pos k` is the position of fw read for the output letter k, and `w` is
  the transform indexed from 0.
* `a n` adds 1 to the 0-based index of the n-th 1 of `w`, so positions count from 1 as in the
  entry; `Nat.nth` counts its argument from 0.
* The excerpt consists of the clause where 1/t + 1/u + 1/v = 1, about the slopes t, u, v that the
  comment names (defined here as there), and the conjecture on the gaps; `main` is the conjunction
  of both. The slopes themselves, as limits of a(n)/n, are named in the comment but are not part
  of the excerpt, and they are not stated here.
-/

namespace OMA.S_oeis_a285682

/-- The Fibonacci morphism 0 -> 01, 1 -> 0 on finite words (any letter other than 0 is sent to 0,
as 1 is). -/
def sig : List ℕ → List ℕ
  | [] => []
  | 0 :: l => 0 :: 1 :: sig l
  | _ :: l => 0 :: sig l

/-- The iterates of the morphism, starting with 0. -/
def fib : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => sig (fib n)

/-- A003849 (offset 0): the infinite Fibonacci word, the limit of the iterates; its letter i is
read off iterate i + 1, which has more than i letters. -/
def fw (i : ℕ) : ℕ := (fib (i + 1)).getD i 0

/-- The scan of StringReplace with the rule 1010 -> 2 on the infinite word fw, read from the left:
`pos k` is the position of fw at which the output letter k (from 0) is produced; if 1010 starts
there it is replaced by 2 and skipped, otherwise the letter is copied. -/
def pos : ℕ → ℕ
  | 0 => 0
  | k + 1 => if fw (pos k) = 1 ∧ fw (pos k + 1) = 0 ∧ fw (pos k + 2) = 1 ∧ fw (pos k + 3) = 0
      then pos k + 4 else pos k + 1

/-- A285680 (0-indexed): the k-th letter of the {1010 -> 2}-transform of the Fibonacci word. -/
def w (k : ℕ) : ℕ :=
  if fw (pos k) = 1 ∧ fw (pos k + 1) = 0 ∧ fw (pos k + 2) = 1 ∧ fw (pos k + 3) = 0 then 2
  else fw (pos k)

/-- A285682(n): the position, counted from 1 as in the entry, of the n-th 1 of A285680. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun k => w k = 1) (n - 1) + 1

/-- The slope the entry names for the positions of 0. -/
noncomputable def t : ℝ := (15 + Real.sqrt 5) / 10

/-- The slope the entry names for the positions of 1. -/
noncomputable def u : ℝ := 4 + Real.sqrt 5

/-- The slope the entry names for the positions of 2. -/
noncomputable def v : ℝ := (1 + 3 * Real.sqrt 5) / 2

/-- Kimberling: 1/t + 1/u + 1/v = 1 for the slopes, and a(n) - a(n-1) is in {5, 7} for n >= 2. -/
theorem main : 1 / t + 1 / u + 1 / v = 1 ∧
    ∀ n : ℕ, 2 ≤ n → a n - a (n - 1) = 5 ∨ a n - a (n - 1) = 7 := by
  sorry

end OMA.S_oeis_a285682
