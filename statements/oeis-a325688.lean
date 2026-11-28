import Mathlib

/-!
# A325688: Number of length-3 compositions of n such that every distinct consecutive subsequence has a different sum.

Source: https://oeis.org/A325688
Credit: @cj-55m (agent: Claude Code, model claude-opus-5-5)

The entry (offset 0, data 0, 0, 0, 1, 0, 4, 5, 12, 12, 25, 24, 40, 41, 60, 60, 85, ...) records in
its FORMULA section, under Conjectures from Colin Barker, May 16 2019:

  G.f.: x^3*(1 + 2*x^2 + 4*x^3 + 5*x^4) / ((1 - x)^3*(1 + x)^2*(1 + x + x^2)).
  a(n) = 2*a(n-2) + a(n-3) - a(n-4) - 2*a(n-5) + a(n-7) for n>7.

Conventions:
* A composition of `n` of length 3 is an ordered triple `(x, y, z)` of positive integers with
  `x + y + z = n` (entry COMMENTS: a composition of n is a finite sequence of positive integers
  summing to n). Every part is at most `n`, so the triples are counted inside `{1, ..., n}^3`;
  this gives `a 0 = 0`, matching the entry (offset 0).
* The consecutive subsequences of `(x, y, z)` are the six nonempty contiguous blocks
  `(x), (y), (z), (x, y), (y, z), (x, y, z)`, taken as lists. The condition every distinct
  consecutive subsequence has a different sum means: any two of these lists with the same sum
  are equal as lists. (The empty block, with sum `0`, could not clash with any other block, so
  leaving it out changes nothing.)
* The g.f. is stated in `PowerSeries ℤ` with the denominator cleared, and the recurrence is
  stated in `ℤ` for every `n > 7`, as in the entry.
-/

namespace OMA.S_oeis_a325688

/-- The nonempty consecutive subsequences of the composition `(x, y, z)`. -/
def consecutive (x y z : ℕ) : List (List ℕ) :=
  [[x], [y], [z], [x, y], [y, z], [x, y, z]]

/-- `a n` is the number of length-3 compositions `(x, y, z)` of `n` in which any two consecutive
subsequences with the same sum are the same subsequence. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun t : ℕ × ℕ × ℕ =>
    t.1 + t.2.1 + t.2.2 = n ∧
      ∀ u ∈ consecutive t.1 t.2.1 t.2.2, ∀ v ∈ consecutive t.1 t.2.1 t.2.2,
        u.sum = v.sum → u = v).card

/-- Colin Barker's conjectured g.f. and recurrence for A325688. -/
theorem main :
    (PowerSeries.mk (fun n => (a n : ℤ)) *
        ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) ^ 2 *
          (1 + PowerSeries.X + PowerSeries.X ^ 2)) =
      (PowerSeries.X : PowerSeries ℤ) ^ 3 *
        (1 + 2 * PowerSeries.X ^ 2 + 4 * PowerSeries.X ^ 3 + 5 * PowerSeries.X ^ 4)) ∧
    ∀ n : ℕ, 7 < n →
      (a n : ℤ) = 2 * a (n - 2) + a (n - 3) - a (n - 4) - 2 * a (n - 5) + a (n - 7) := by
  sorry

end OMA.S_oeis_a325688
