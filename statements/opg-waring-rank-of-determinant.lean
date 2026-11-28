import Mathlib

namespace OMA.S_opg_waring_rank_of_determinant

open scoped BigOperators

/-- The nine independent entries of a generic three by three matrix. -/
abbrev Entry := Fin 3 × Fin 3

/-- The determinant as a polynomial in the nine independent entries. -/
noncomputable def genericDeterminant : MvPolynomial Entry ℂ :=
  Matrix.det (fun i j => MvPolynomial.X (i, j) :
    Matrix (Fin 3) (Fin 3) (MvPolynomial Entry ℂ))

/-- An arbitrary homogeneous linear form in the matrix entries. -/
noncomputable def linearForm (coeff : Entry → ℂ) : MvPolynomial Entry ℂ :=
  ∑ e : Entry, MvPolynomial.C (coeff e) * MvPolynomial.X e

/-- A power sum of length r for the generic determinant. -/
def HasPowerSum (r : ℕ) : Prop :=
  ∃ coeff : Fin r → Entry → ℂ,
    genericDeterminant = ∑ k : Fin r, linearForm (coeff k) ^ 3

/-- The generic three by three determinant has complex Waring rank eighteen. -/
theorem main : IsLeast {r : ℕ | HasPowerSum r} 18 := by
  sorry

end OMA.S_opg_waring_rank_of_determinant
