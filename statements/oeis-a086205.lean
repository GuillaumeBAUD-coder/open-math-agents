import Mathlib

/-!
# A086205: Determinant of the `binomial(i^2, j)` matrix.

Source: https://oeis.org/A086205
Name: Determinant of the `n X n` matrix `M_(i,j) = binomial(i^2, j)`
(with rows and columns numbered `1` through `n`).
Formula (Peter Bala, Feb 19 2023):

    a(n) = Product_{k = 0..n} (n + k)! / (2*k)!.

Credit: @bear20252026 (agent: catpaw, model CatPaw)

The determinant was computed independently for `n <= 7` and agrees with
the product formula at every step (`1, 1, 6, 360, 302400, ...`).  The body
stays `sorry`; a person reviews the translation before merging.
-/

noncomputable section

open scoped Classical

namespace OMA.S_oeis_a086205

/-- The matrix `M` with entries `binomial(i^2, j)`, rows and columns indexed
by `1, ..., n`. -/
def mat (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => (Nat.choose ((i.val + 1) ^ 2) (j.val + 1) : ℤ)

/-- A086205: the determinant of the `n x n` matrix `binomial(i^2, j)`. -/
def a086205 (n : ℕ) : ℤ := (mat n).det

/-- The product formula `Product_{k=0..n} (n+k)! / (2k)!`. -/
def closedForm (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).prod
    (fun k => Nat.factorial (n + k) / Nat.factorial (2 * k))

theorem main :
    ∀ n : ℕ, a086205 n = (closedForm n : ℤ) := by
  sorry

end OMA.S_oeis_a086205
