import Mathlib

/-!
# Determinant of a rank r perturbation

MathOverflow question 311620 by tisPrimeTime asks for the squared-minor expansion
of the secular determinant in *Restricted Rank Modification of the Symmetric
Eigenvalue Problem: Theoretical Considerations*. The selected rows and columns
are matched in increasing order. The empty row and column sets give the constant
term one, and sets of different cardinalities contribute zero.

Source: https://mathoverflow.net/questions/311620
-/

namespace OMA.S_mo_311620

/-- Match the ordered columns of a minor to its ordered rows. -/
noncomputable def rowEquiv {n r : ℕ} (T : Finset (Fin r)) (J : Finset (Fin n))
    (h : T.card = J.card) : T ≃ J :=
  (T.orderIsoOfFin rfl).toEquiv.symm.trans (J.orderIsoOfFin h.symm).toEquiv

/-- Square of the determinant of the submatrix with rows `J` and columns `T`. -/
noncomputable def minorSq {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (J : Finset (Fin n)) (T : Finset (Fin r)) : ℝ :=
  if h : T.card = J.card then
    (U.submatrix (fun i : T => (rowEquiv T J h i : Fin n))
      (fun j : T => (j : Fin r))).det ^ 2
  else 0

/-- Away from the spectral poles, the rank-`r` secular determinant is the sum of
squared minors with alternating signs and products of spectral gaps in the denominator. -/
theorem main : ∀ (n r : ℕ) (U : Matrix (Fin n) (Fin r) ℝ) (eigenvalue : Fin n → ℝ)
    (t : ℝ), (∀ i, t ≠ eigenvalue i) →
    (1 - U.transpose * Matrix.diagonal (fun i => (t - eigenvalue i)⁻¹) * U).det =
      ∑ T : Finset (Fin r), ∑ J : Finset (Fin n),
        (-1 : ℝ) ^ T.card * minorSq U J T / ∏ j ∈ J, (t - eigenvalue j) := by
  sorry

end OMA.S_mo_311620
