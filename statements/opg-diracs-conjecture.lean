import Mathlib

/-!
# Dirac's Conjecture

Source: https://www.openproblemgarden.org/op/diracs_conjecture
Credit: @Hyvok

*Poser:* G. A. Dirac. *Reference:* G. A. Dirac, Collinearity properties of sets of points,
Quart. J. Math. Oxford Ser. (2) 2 (1951), 221–227. See also J. Beck (Combinatorica 1983),
E. Szemerédi and W. T. Trotter (Combinatorica 1983), M. S. Payne and D. R. Wood, Progress on
Dirac's Conjecture (Electron. J. Combin. 2014), Z. Han, A Note on Weak Dirac Conjecture
(Electron. J. Combin. 2017).

**Conjecture (as in the source).** There is a constant `c` such that for every set `P` of `n`
points in the plane, not all on one line, some point of `P` lies on at least `n/2 - c` lines
determined by `P`. A line is determined by `P` if it contains at least two points of `P`.

## Formalization notes

* The plane is `EuclideanSpace ℝ (Fin 2)`; `P` is a `Finset` of points and `n = P.card`.
* Not all on one line is `¬ Collinear ℝ (P : Set _)` (Mathlib's `Collinear`).
* The lines determined by `P` that pass through `p ∈ P` are exactly the affine lines
  `line[ℝ, p, q]` for `q ∈ P` with `q ≠ p`; `linesThrough P p` is the finset of these
  (as `AffineSubspace`s, so equal lines are counted once), and its cardinality is the number of
  determined lines incident to `p`.
* The constant `c` is a single real number, chosen before `P` (uniform over all `P` and `n`);
  no sign condition is imposed on it. The inequality is `n / 2 - c ≤ #lines` in `ℝ`.
-/

namespace OMA.S_opg_diracs_conjecture

open scoped Classical

/-- The lines determined by `P` passing through `p`: the lines through `p` and another point
of `P`. -/
noncomputable def linesThrough (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (p : EuclideanSpace ℝ (Fin 2)) : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) :=
  (P.erase p).image fun q => line[ℝ, p, q]

/-- **Dirac's conjecture.** -/
theorem main : ∃ c : ℝ, ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
    ¬ Collinear ℝ (P : Set (EuclideanSpace ℝ (Fin 2))) →
    ∃ p ∈ P, (P.card : ℝ) / 2 - c ≤ ((linesThrough P p).card : ℝ) := by
  sorry

end OMA.S_opg_diracs_conjecture
