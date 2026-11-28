import OMAStatements.S_mo_159879
import Mathlib

/-!
# MathOverflow 159879: Fourier coefficients of a positive semidefinite quadratic form on the cube

For `b ∈ {±1}ⁿ` the function `b ↦ bᵀ B b` has Fourier coefficient `tr B` at `S = ∅`,
`B i j + B j i` at `S = {i, j}`, and `0` elsewhere. So both universal claims fail:

* `n = 1`, `B = 1`, `S = {0}`: the coefficient is `(1/2) (1 · 1 + 1 · (-1)) = 0`.
* `n = 2`, `B = a aᵀ` with `a = (1, -1)` (positive semidefinite), `S = {0, 1}`: the coefficient is
  `(1/4) (0 - 4 - 4 + 0) = -2 < 0`.
-/

open Matrix OMA.S_mo_159879

namespace OMA.MO159879

/-- Sum over sign patterns of length `1`. -/
lemma sum_fin_one (F : (Fin 1 → Bool) → ℝ) :
    ∑ b : Fin 1 → Bool, F b = F (fun _ => false) + F (fun _ => true) := by
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
  simp [add_comm]
  rfl

/-- Sum over sign patterns of length `2`. -/
lemma sum_fin_two (F : (Fin 2 → Bool) → ℝ) :
    ∑ b : Fin 2 → Bool, F b
      = F ![true, true] + F ![true, false] + F ![false, true] + F ![false, false] := by
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    Fintype.sum_bool, Fintype.sum_bool]
  simp [finTwoArrowEquiv]
  ring

/-- The first counterexample: a vanishing coefficient. -/
lemma coeff_one : coefficient (1 : Matrix (Fin 1) (Fin 1) ℝ) {0} = 0 := by
  unfold coefficient
  rw [sum_fin_one]
  simp [signVector, sign, dotProduct, mulVec]

/-- The second counterexample: a negative coefficient. -/
lemma coeff_two :
    coefficient (vecMulVec ![(1 : ℝ), -1] (star ![(1 : ℝ), -1])) Finset.univ = -2 := by
  unfold coefficient
  rw [sum_fin_two]
  simp [signVector, sign, dotProduct, mulVec, vecMulVec, Fin.sum_univ_two, Fin.prod_univ_two]
  norm_num

end OMA.MO159879

open OMA.MO159879 in
theorem OMA.solution : type_of% @OMA.S_mo_159879.main := by
  constructor
  · intro h
    exact h 1 1 Matrix.PosSemidef.one {0} coeff_one
  · intro h
    have := h 2 _ (Matrix.posSemidef_vecMulVec_self_star ![(1 : ℝ), -1]) Finset.univ
    rw [coeff_two] at this
    norm_num at this
