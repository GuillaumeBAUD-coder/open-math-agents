import Mathlib

/-!
# A081200: 6th binomial transform of (0,1,0,1,0,1,...), A000035

Source: https://oeis.org/A081200
Credit: @xor2k
Sibling of OEIS A081201 (same conjecture wording); statement modelled on the accepted one for that entry.

Formalizes the conjecture of R. H. Hardin (May 24 2010) recorded in OEIS A081200 (offset 0):
Conjecture (verified up to a(9)): Number of collinear 5-tuples of points in a 5 X 5 X 5 X ...
n-dimensional cubic grid.

Conventions: A081200 is the 6th binomial transform of A000035, whose closed form recorded in the
entry is `a(n) = 7^n/2 - 5^n/2`; it is written as `(7^n - 5^n) / 2` in `ℕ` (the difference is even,
so the floor division is exact). The grid point `p : Fin n → Fin 5` is viewed as the real point
`fun i => (p i : ℝ)`, and a 5-tuple is an unordered set of 5 distinct grid points; it is collinear
when its image is `Collinear ℝ` in `Fin n → ℝ`. This matches the data: `a 0 = 0` (one point),
`a 1 = 1`, and `a 2 = 12` (5 rows, 5 columns, 2 diagonals). The conjecture is stated for all `n ≥ 0`.
-/

namespace OMA.S_oeis_a081200

/-- The grid point `p` of `{0, ..., 4}^n` as a point of `ℝ^n`. -/
def toReal {n : ℕ} (p : Fin n → Fin 5) : Fin n → ℝ := fun i => ((p i : ℕ) : ℝ)

/-- The number of collinear `5`-element sets of points of the `5^n` grid. -/
noncomputable def lineCount (n : ℕ) : ℕ :=
  {s : Finset (Fin n → Fin 5) | s.card = 5 ∧ Collinear ℝ (toReal '' (s : Set (Fin n → Fin 5)))}.ncard

/-- Hardin's conjecture: the count equals A081200(n) = (7^n - 5^n)/2 for every `n`. -/
theorem main : ∀ n : ℕ, lineCount n = (7 ^ n - 5 ^ n) / 2 := by
  sorry

end OMA.S_oeis_a081200
