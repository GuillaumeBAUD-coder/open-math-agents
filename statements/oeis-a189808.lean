import Mathlib

/-!
# OEIS A189808: Barker's conjectures for the number of right triangles on an (n+1) X 4 grid

Source: https://oeis.org/A189808 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jaredwilder.

Entry A189808 (R. H. Hardin, Apr 28 2011), offset 1: Number of right triangles on a (n+1) X 4 grid.
Data: 28, 94, 200, 342, 524, 732, 972, 1236, 1524, 1840, ...
Formula section:
Empirical: a(n) = 12*n^2 + 88*n - 240 for n>8.
Conjectures from Colin Barker, May 03 2018: (Start)
G.f.: 2*x*(14 + 5*x + x^2 - 2*x^3 + 2*x^4 - 7*x^5 + 3*x^6 - 4*x^7 + 2*x^9 - 2*x^10) / (1 - x)^3.
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>8.
(End)

Formalization notes:
* The grid is the set of points (x, y) with 0 <= x <= n and 0 <= y <= 3 ((n+1) X 4 points). A right
  triangle is a set of three grid points one of which, p, sees the other two, q and r, at a right
  angle: (q - p) . (r - p) = 0. Three distinct points with a right angle are never collinear.
* The definition also makes sense at n = 0, where the 1 X 4 grid is a line and the count is 0;
  this is the coefficient of x^0 in the g.f. (which starts at x^1), so the g.f. is stated for
  mk a over the integers as A * D = N (D has constant term 1).
* The statement is the conjunction of Barker's conjectures: the recurrence (for n > 8, in the
  integers) and the g.f.
* Controls: the definition gives 0, 28, 94, 200, 342, 524, 732, 972 for n = 0..7 (direct
  enumeration), the entry's data from n = 1.
-/

namespace OMA.S_oeis_a189808

open PowerSeries

/-- The points of the (n+1) X 4 grid. -/
def grid (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range (n + 1) ×ˢ Finset.range 4).image fun p => ((p.1 : ℤ), (p.2 : ℤ))

/-- A set of points is a right triangle: three distinct points with a right angle at one of them. -/
def IsRight (s : Finset (ℤ × ℤ)) : Prop :=
  ∃ p ∈ s, ∃ q ∈ s, ∃ r ∈ s, p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
    (q.1 - p.1) * (r.1 - p.1) + (q.2 - p.2) * (r.2 - p.2) = 0

instance : DecidablePred IsRight := fun s => by unfold IsRight; infer_instance

/-- A189808(n): the number of right triangles on the (n+1) X 4 grid. -/
def a (n : ℕ) : ℕ := (((grid n).powersetCard 3).filter IsRight).card

/-- Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 8 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3) =
      (2 * X * (14 + 5 * X + X ^ 2 - 2 * X ^ 3 + 2 * X ^ 4 - 7 * X ^ 5 + 3 * X ^ 6 - 4 * X ^ 7 + 2 * X ^ 9 - 2 * X ^ 10) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a189808
