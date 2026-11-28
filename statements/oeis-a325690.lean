import Mathlib

/-!
# A325690: Number of length-3 integer partitions of n whose largest part is not the sum of the other two.

Source: https://oeis.org/A325690
Credit: @cj-55m (agent: Claude Code, model claude-opus-5-5)

The entry (offset 0, data 0, 0, 0, 1, 0, 2, 2, 4, 3, 7, 6, 10, 9, 14, 13, 19, 17, 24, ...)
records in its FORMULA section, under Conjectures from Colin Barker, May 15 2019:

  G.f.: x^3*(1 + x^2 + x^3 + x^4) / ((1 - x)^3*(1 + x)^2*(1 + x^2)*(1 + x + x^2)).
  a(n) = a(n-2) + a(n-3) + a(n-4) - a(n-5) - a(n-6) - a(n-7) + a(n-9) for n>8.

Conventions:
* A length-3 integer partition of `n` is written as a triple `(x, y, z)` of positive integers
  with `x ≥ y ≥ z` and `x + y + z = n`; its largest part is `x`. The sequence `a n` counts those
  triples with `x ≠ y + z`. Every part is at most `n`, so the triples are counted inside
  `{1, ..., n}^3`; this gives `a 0 = 0`, matching the entry (offset 0).
* The recurrence is read in `ℤ` and claimed for every `n > 8`, as in the entry (all indices
  `n - 2, ..., n - 9` are then natural numbers).
* The generating function is stated in `PowerSeries ℤ` with the denominator multiplied out:
  the series `∑ a n * X^n` times `(1 - X)^3 * (1 + X)^2 * (1 + X^2) * (1 + X + X^2)` equals
  `X^3 * (1 + X^2 + X^3 + X^4)`. Since the denominator has constant coefficient `1`, this is
  equivalent to the stated g.f.
-/

namespace OMA.S_oeis_a325690

/-- `a n` is the number of length-3 partitions `x ≥ y ≥ z ≥ 1` of `n` whose largest part `x` is
not the sum `y + z` of the other two. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun t : ℕ × ℕ × ℕ =>
    t.1 + t.2.1 + t.2.2 = n ∧ t.2.2 ≤ t.2.1 ∧ t.2.1 ≤ t.1 ∧ t.1 ≠ t.2.1 + t.2.2).card

open PowerSeries in
/-- Colin Barker's conjectured recurrence and generating function for A325690. -/
theorem main :
    (∀ n : ℕ, 8 < n →
      (a n : ℤ) = a (n - 2) + a (n - 3) + a (n - 4) - a (n - 5) - a (n - 6) - a (n - 7) +
        a (n - 9)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) *
        ((1 - X) ^ 3 * (1 + X) ^ 2 * (1 + X ^ 2) * (1 + X + X ^ 2)) =
      X ^ 3 * (1 + X ^ 2 + X ^ 3 + X ^ 4) := by
  sorry

end OMA.S_oeis_a325690
