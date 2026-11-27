import FormalConjectures.Wikipedia.Jacobson

theorem OMA.solution : type_of% @Jacobson.jacobson_conjecture_of_comm_ring := by
  intro R _ _
  show ⨅ n : ℕ, Ring.jacobson R ^ n = 0
  simpa only [smul_eq_mul, Ideal.mul_top, Submodule.zero_eq_bot] using
    (Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := R) (Ring.jacobson R)
      (by rw [Ideal.jacobson_bot]))
