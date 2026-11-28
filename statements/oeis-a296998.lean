import Mathlib

/-!
# A296998: Four points on an `n × n` grid with no three in arithmetic progression.

Source: https://oeis.org/A296998
Name: Number of ways to place 4 points on an `n X n` point grid so that no
point is equally distant from two other points on the same row or the same
column.
Conjecture (Colin Barker, Dec 23 2017): with `a(n)` denoting this number,
for `n > 21`,

    a(n) = 3*a(n-1) - a(n-2) - 3*a(n-3) + a(n-4) - 3*a(n-5) + 8*a(n-6)
           - 2*a(n-8) - 2*a(n-9) - 10*a(n-10) + 10*a(n-11) + 2*a(n-12)
           + 2*a(n-13) - 8*a(n-15) + 3*a(n-16) - a(n-17) + 3*a(n-18)
           + a(n-19) - 3*a(n-20) + a(n-21).

Credit: @bear20252026 (agent: catpaw, model CatPaw)

A placement is a set of four distinct grid points, encoded as a `Finset` of
elements of `Fin n × Fin n`.  A point is equally distant from two other
points on a common row exactly when its first coordinate is the average of
the first coordinates of those two points (and similarly for a column), so
the forbidden configurations are triples of chosen points lying in a common
row or column whose middle coordinate is the average of the outer two, i.e.
3-term arithmetic progressions in some row or column.  The combinatorial
definition was brute-force checked against the OEIS data for `n ≤ 5`, and
the recurrence above was checked against the b-file values for
`22 ≤ n ≤ 40`.  The body stays `sorry`; a person reviews the translation
before merging.
-/

noncomputable section

open scoped Classical

namespace OMA.S_oeis_a296998

abbrev Grid (n : ℕ) := Fin n × Fin n

/-- Three distinct grid points form a forbidden triple when they share a row
and one first coordinate is the midpoint of the other two, or they share a
column and one second coordinate is the midpoint of the other two. -/
def badTriple (n : ℕ) (p q r : Grid n) : Prop :=
  (p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
    p.2 = q.2 ∧ q.2 = r.2 ∧ p.1.val + r.1.val = 2 * q.1.val) ∨
  (p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
    p.1 = q.1 ∧ q.1 = r.1 ∧ p.2.val + r.2.val = 2 * q.2.val)

/-- A placement of four points is admissible when it contains no forbidden
triple. -/
def good (n : ℕ) (s : Finset (Grid n)) : Prop :=
  s.card = 4 ∧ ∀ p ∈ s, ∀ q ∈ s, ∀ r ∈ s, ¬ badTriple n p q r

/-- All finite subsets of the `n × n` grid. -/
def subsets (n : ℕ) : Finset (Finset (Grid n)) :=
  (Finset.univ : Finset (Grid n)).powerset

/-- A296998: the number of admissible placements of four points on the
`n × n` grid. -/
def a296998 (n : ℕ) : ℕ := (subsets n).filter (good n) |>.card

theorem main :
    ∀ n : ℕ, 21 < n →
      a296998 n =
        3 * a296998 (n - 1) - a296998 (n - 2) - 3 * a296998 (n - 3) +
          a296998 (n - 4) - 3 * a296998 (n - 5) + 8 * a296998 (n - 6) -
          2 * a296998 (n - 8) - 2 * a296998 (n - 9) - 10 * a296998 (n - 10) +
          10 * a296998 (n - 11) + 2 * a296998 (n - 12) + 2 * a296998 (n - 13) -
          8 * a296998 (n - 15) + 3 * a296998 (n - 16) - a296998 (n - 17) +
          3 * a296998 (n - 18) + a296998 (n - 19) - 3 * a296998 (n - 20) +
          a296998 (n - 21) := by
  sorry

end OMA.S_oeis_a296998
