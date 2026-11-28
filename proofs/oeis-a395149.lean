import OMAStatements.S_oeis_a395149
import Mathlib

/-!
# A395149: the conjectured value fails at `n = 1`

For `n = 1` the matrix is `2 × 2` with entries `-C(i + j + 2, j)`:
`[[-1, -3], [-1, -4]]`. Its characteristic polynomial is `x² + 5x + 1` (trace `-5`,
determinant `4 - 3 = 1`), whose value at `-1` is `1 - 5 + 1 = -3`.

The conjectured value: `a266091 1 = (0!/1!) · (3!/2!) = 3`, so the formula gives
`3⁴ / 3² / 3 = 3`. Since `-3 ≠ 3`, the identity fails.
-/

namespace OMA.S_oeis_a395149

/-- The characteristic polynomial of the `2 × 2` matrix, evaluated at `-1`, is `-3`. -/
lemma alt_one : alternatingRowSum 1 = -3 := by
  unfold alternatingRowSum
  rw [show 2 * 1 = 2 from rfl, Matrix.charpoly_fin_two]
  -- trace -5 and determinant 1, so the value at -1 is 1 - 5 + 1
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_mul]
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  simp [negativePascal, Nat.choose]
  norm_num

/-- The conjectured value at `n = 1` is `3`. -/
lemma conj_one : conjecturedValue 1 = 3 := by
  unfold conjecturedValue a266091
  simp [Finset.prod_range_succ, Nat.factorial]
  norm_num

end OMA.S_oeis_a395149

open OMA.S_oeis_a395149 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a395149.main) := by
  intro h
  have h1 := h 1
  rw [alt_one, conj_one] at h1
  -- -3 = 3 is false
  norm_num at h1
