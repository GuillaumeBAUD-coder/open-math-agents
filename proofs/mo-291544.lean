import OMAStatements.S_mo_291544

theorem OMA.solution : type_of% @OMA.S_mo_291544.main := by
  intro A x
  simp only [Matrix.det_fin_three, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul, mul_one]
  have h := sq_nonneg (x * (A 0 0 * A 1 1 - A 0 0 * A 1 2 - A 0 0 * A 2 1 + A 0 0 * A 2 2
    - A 0 1 * A 1 0 + A 0 1 * A 1 2 + A 0 1 * A 2 0 - A 0 1 * A 2 2 + A 0 2 * A 1 0
    - A 0 2 * A 1 1 - A 0 2 * A 2 0 + A 0 2 * A 2 1 + A 1 0 * A 2 1 - A 1 0 * A 2 2
    - A 1 1 * A 2 0 + A 1 1 * A 2 2 + A 1 2 * A 2 0 - A 1 2 * A 2 1))
  linear_combination h
