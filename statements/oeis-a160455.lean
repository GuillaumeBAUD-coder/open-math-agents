import Mathlib

/-!
# OEIS A160455: triangles built from all rods of lengths 1, ..., n

Source: https://oeis.org/A160455
Credit: Sudharsan Rajendiran

A160455(n) is the number of triangles that can be built from rods with lengths `1, 2, ..., n` by
using and concatenating all rods. Equivalently (as in the OEIS comments) it is the number of triples
of side lengths `(a, b, c)` with `a ≥ b ≥ c > 0` and `b + c > a` (a nondegenerate triangle) such
that `{1, ..., n}` splits into three pairwise disjoint sets, together using every rod, with element
sums `a`, `b` and `c`. Colin Barker conjectured (May 2019) the g.f.
`x^4 (2 - x + 2x^2 - 3x^3 + 6x^4 - 5x^5 + 8x^6 - 9x^7 + 11x^8 - 11x^9 + 11x^10 - 10x^11 + 10x^12
- 8x^13 + 5x^14 - 3x^15 + x^16) / ((1 - x)^5 (1 + x^2)^3 (1 + x + x^2) (1 + x^4))`.
We state it as an identity of formal power series over `ℚ` with the denominator multiplied across.

Conventions: the rods are `Finset.Icc 1 n`. The OEIS offset is 3; we define `a n` for every `n`
by the same formula, which gives `a 0 = a 1 = a 2 = a 3 = 0`, matching the factor `x^4`. Since all
rods are used, every side is at most the total length `n (n + 1) / 2`, so the triples are searched
in the box `[0, n (n + 1) / 2]^3`.
-/

namespace OMA.S_oeis_a160455

/-- The rods `1, ..., n` can be split into three pairwise disjoint groups, together using every
rod, whose total lengths are `a`, `b` and `c`. -/
def Buildable (n a b c : ℕ) : Prop :=
  ∃ A B C : Finset ℕ, Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧ A ∪ B ∪ C = Finset.Icc 1 n ∧
    ∑ i ∈ A, i = a ∧ ∑ i ∈ B, i = b ∧ ∑ i ∈ C, i = c

open Classical in
/-- A160455(n): the number of triangles with sides `a ≥ b ≥ c > 0`, `b + c > a`, that can be built
from all the rods `1, ..., n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.range (n * (n + 1) / 2 + 1) ×ˢ Finset.range (n * (n + 1) / 2 + 1) ×ˢ
      Finset.range (n * (n + 1) / 2 + 1)).filter (fun t : ℕ × ℕ × ℕ =>
        0 < t.2.2 ∧ t.2.2 ≤ t.2.1 ∧ t.2.1 ≤ t.1 ∧ t.1 < t.2.1 + t.2.2 ∧
          Buildable n t.1 t.2.1 t.2.2)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) *
        ((1 - X) ^ 5 * (1 + X ^ 2) ^ 3 * (1 + X + X ^ 2) * (1 + X ^ 4)) =
      X ^ 4 * (2 - X + 2 * X ^ 2 - 3 * X ^ 3 + 6 * X ^ 4 - 5 * X ^ 5 + 8 * X ^ 6 - 9 * X ^ 7 +
        11 * X ^ 8 - 11 * X ^ 9 + 11 * X ^ 10 - 10 * X ^ 11 + 10 * X ^ 12 - 8 * X ^ 13 +
        5 * X ^ 14 - 3 * X ^ 15 + X ^ 16) := by
  sorry

end OMA.S_oeis_a160455
