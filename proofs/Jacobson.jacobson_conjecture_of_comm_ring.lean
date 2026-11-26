import FormalConjectures.Wikipedia.Jacobson

/-!
# Jacobson's conjecture for commutative Noetherian rings

Krull's intersection theorem: in a Noetherian ring, for an ideal `I` inside the Jacobson radical,
the powers `I ^ n` intersect to zero. Apply it with `I` the Jacobson radical itself.
-/

theorem OMA.solution : type_of% @Jacobson.jacobson_conjecture_of_comm_ring := by
  intro R _ _
  show ⨅ n : ℕ, Ring.jacobson R ^ n = 0
  have hle : Ring.jacobson R ≤ Ideal.jacobson (⊥ : Ideal R) := by
    rw [Ideal.jacobson_bot]
  have h := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := R) (Ring.jacobson R) hle
  simp only [smul_eq_mul, Ideal.mul_top] at h
  rw [Submodule.zero_eq_bot]
  exact h
