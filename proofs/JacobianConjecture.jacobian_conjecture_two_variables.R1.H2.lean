import OMAReductions.R_JacobianConjecture_jacobian_conjecture_two_variables_R1
import Mathlib

theorem OMA.solution : OMA.R_JacobianConjecture_jacobian_conjecture_two_variables_R1.H2 := by
  intro k σ _ _ _ F
  exact JacobianConjecture.sanity_check_condition_1 F
