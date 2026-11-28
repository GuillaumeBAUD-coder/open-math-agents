import Mathlib

/-!
# Sphere packing

Source: https://en.wikipedia.org/wiki/Sphere_packing
-- Credit: @mbilenko03 (agent: antigravity, model grok-4.7)

Wikipedia problem. A sphere packing in Euclidean `n`-space is an arrangement of
non-overlapping balls of equal radius. Its upper density is the limsup, as
`R → ∞`, of the fraction of the ball of radius `R` covered by the packing. The
maximal density `spherePackingDensity n` is the supremum of that upper density
over all such packings.

The density is known for `n ∈ {1, 2, 3, 8, 24}`: the interval, the hexagonal
lattice, the Kepler packing, the `E₈` lattice, and the Leech lattice. It is an
open problem to determine `spherePackingDensity n` for every
`n ∉ {1, 2, 3, 8, 24}`, and to determine the asymptotic behaviour of this
maximal density as `n → ∞` (the best proved bounds are of shape
`c n / 2 ^ n` from below and `2 ^ (-(0.599 + o(1)) n)` from above, with sharper
recent lower bounds, but the true growth rate is unknown).

`theorem main` records the standard conjecture in the first four open
dimensions, `n = 4, 5, 6, 7`, which sit after the solved cases `1, 2, 3` and
before Viazovska's theorem in dimensions `8` and `24`. In each of these
dimensions the best packing known is a root lattice, and the conjecture is that
its density is optimal among all packings, lattice or not:

* `n = 4`: the `D₄` root lattice.
* `n = 5`: the `D₅` root lattice.
* `n = 6`: the `E₆` root lattice.
* `n = 7`: the `E₇` root lattice.

No single closed form is conjectured for a general remaining dimension, so
`main` states these four concrete equalities. The definitions below are the
general packing density in every dimension; the rest of the Wikipedia problem
is the identification of that function off `{1, 2, 3, 8, 24}` and its growth
as `n → ∞`.

Conventions, matching the other packing statements in this catalogue:
* Centers live in `EuclideanSpace ℝ (Fin n)`.
* `IsSpherePacking` is a set of centers of balls of radius `1` with pairwise
  disjoint interiors, equivalently pairwise distance at least `2`.
* `upperDensity` is
  `limsup_{R → ∞} vol(⋃ balls ∩ B(0, R)) / vol(B(0, R))`,
  with Lebesgue measure `volume` on `EuclideanSpace ℝ (Fin n)`.
* `spherePackingDensity n` is the supremum of `upperDensity` over all such
  packings. The empty packing has density `0`, and every packing has upper
  density at most `1`, so the supremum is a real number in `[0, 1]`.

The four constants are `vol(B_n) / covol(L_n)` for the root lattice scaled so
that its minimal vector has length `2`. Unscaled, `Dₙ` (`n ≥ 2`), `E₆`, and
`E₇` have minimal norm `√2` and covolumes `2`, `√3`, and `√2`. Scaling by `√2`
multiplies the covolume by `(√2) ^ n`. The ball of radius `1` has volume
`π ^ (n / 2) / Γ(n / 2 + 1)`.

* `n = 4`: `(π ^ 2 / 2) / (2 * (√2) ^ 4) = π ^ 2 / 16`.
* `n = 5`: `(8 * π ^ 2 / 15) / (2 * (√2) ^ 5) = π ^ 2 / (15 * √2) = π ^ 2 * √2 / 30`.
* `n = 6`: `(π ^ 3 / 6) / (√3 * (√2) ^ 6) = π ^ 3 / (48 * √3)`.
* `n = 7`: `(16 * π ^ 3 / 105) / (√2 * (√2) ^ 7) = π ^ 3 / 105`.
-/

namespace OMA.S_wp_sphere_packing

open MeasureTheory

/-- Centers of radius-`1` balls with pairwise disjoint interiors. -/
def IsSpherePacking (n : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 2 ≤ dist x y

/-- Upper density of the radius-`1` balls centered at `C`. -/
noncomputable def upperDensity (n : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  Filter.limsup (fun R : ℝ =>
    (volume ((⋃ x ∈ C, Metric.ball x 1) ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)).toReal /
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)).toReal) Filter.atTop

/-- Maximal upper density of an equal-ball packing in dimension `n`. -/
noncomputable def spherePackingDensity (n : ℕ) : ℝ :=
  sSup { d : ℝ | ∃ C : Set (EuclideanSpace ℝ (Fin n)),
    IsSpherePacking n C ∧ d = upperDensity n C }

/-- The root lattices `D₄`, `D₅`, `E₆`, and `E₇` are optimal in dimensions 4–7. -/
theorem main :
    spherePackingDensity 4 = Real.pi ^ 2 / 16 ∧
      spherePackingDensity 5 = Real.pi ^ 2 * Real.sqrt 2 / 30 ∧
      spherePackingDensity 6 = Real.pi ^ 3 / (48 * Real.sqrt 3) ∧
      spherePackingDensity 7 = Real.pi ^ 3 / 105 := by
  sorry

end OMA.S_wp_sphere_packing
