import Mathlib

/-!
# What is the smallest sphere whose surface includes 100 integer points?

The source: "Let S(r) be the surface of the origin-centered sphere in ℝ³. A point is an integer
point if all its coordinates are integers. What is the smallest radius r_n such that S(r_n)
includes ≥ n integer points?" The title asks for the case n = 100.

Reading choices:
* The sphere is centred at the origin, as the question body says (off-origin spheres, discussed in
  an answer, are not part of the question).
* The radius is a real number r ≥ 0, and the integer points on S(r) are the triples
  (x, y, z) ∈ ℤ³ with x² + y² + z² = r² (computed in ℝ); "includes ≥ 100 points" is
  `100 ≤ Set.ncard`, and this set is always finite, so `ncard` is its true cardinality.
* Only the title case n = 100 is formalized; the growth-rate and algorithm questions are not
  precise yes/no claims.
* The claim: √74 is the least such radius.

How the source settles it: the update at the end of the question states that "a sphere of radius
√74 ≈ 8.6 includes 120 integer points on its surface, and smaller spheres include fewer than 100
points"; the value 74 and the count 120 come from the second-highest-voted answer (score 9). The
formal proof checks both facts by a finite count.

Source: https://mathoverflow.net/questions/291754/what-is-the-smallest-sphere-whose-surface-includes-100-integer-points
Credit: @xor2k
-/

namespace OMA.S_mo_291754

/-- The integer points on the origin-centred sphere of radius `r` in `ℝ³`. -/
def spherePoints (r : ℝ) : Set (ℤ × ℤ × ℤ) :=
  {p | ((p.1 : ℝ) ^ 2 + (p.2.1 : ℝ) ^ 2 + (p.2.2 : ℝ) ^ 2) = r ^ 2}

theorem main :
    IsLeast {r : ℝ | 0 ≤ r ∧ 100 ≤ (spherePoints r).ncard} (Real.sqrt 74) := by
  sorry

end OMA.S_mo_291754
