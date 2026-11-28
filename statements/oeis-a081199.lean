import Mathlib

/-!
# A081199: 5th binomial transform of (0,1,0,1,...), A000035

Source: https://oeis.org/A081199
Credit: @xor2k
Sibling of OEIS A081201 (same conjecture wording); statement modelled on the accepted one for that entry.

Formalizes the conjecture of R. H. Hardin (May 24 2010) recorded in OEIS A081199 (offset 0):
Conjecture (verified up to a(9)): Number of collinear 4-tuples of points in a 4 X 4 X 4 X ...
n-dimensional cubic grid.

Conventions: A081199 is the 5th binomial transform of A000035, whose closed form recorded in the
entry is `a(n) = 6^n/2 - 4^n/2`; it is written as `(6^n - 4^n) / 2` in `ℕ` (the difference is even,
so the floor division is exact). The grid point `p : Fin n → Fin 4` is viewed as the real point
`fun i => (p i : ℝ)`, and a 4-tuple is an unordered set of 4 distinct grid points; it is collinear
when its image is `Collinear ℝ` in `Fin n → ℝ`. This matches the data: `a 0 = 0` (one point),
`a 1 = 1`, and `a 2 = 10` (4 rows, 4 columns, 2 diagonals). The conjecture is stated for all `n ≥ 0`.
-/

namespace OMA.S_oeis_a081199

/-- The grid point `p` of `{0, ..., 3}^n` as a point of `ℝ^n`. -/
def toReal {n : ℕ} (p : Fin n → Fin 4) : Fin n → ℝ := fun i => ((p i : ℕ) : ℝ)

/-- The number of collinear `4`-element sets of points of the `4^n` grid. -/
noncomputable def lineCount (n : ℕ) : ℕ :=
  {s : Finset (Fin n → Fin 4) | s.card = 4 ∧ Collinear ℝ (toReal '' (s : Set (Fin n → Fin 4)))}.ncard

/-- Hardin's conjecture: the count equals A081199(n) = (6^n - 4^n)/2 for every `n`. -/
theorem main : ∀ n : ℕ, lineCount n = (6 ^ n - 4 ^ n) / 2 := by
  sorry

end OMA.S_oeis_a081199
