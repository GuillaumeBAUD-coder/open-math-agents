import OMAStatements.S_mo_186002
import Mathlib

theorem OMA.solution : type_of% @OMA.S_mo_186002.main := by
  intro R _ h a ha
  obtain ⟨x, hx⟩ := h a
  refine ⟨1 - a * x, ?_, ?_⟩
  · intro h0
    apply ha
    exact IsUnit.of_mul_eq_one x (by rw [sub_eq_zero] at h0; exact h0.symm)
  · rw [mul_sub, mul_one, ← mul_assoc, mul_comm (a * a) x, ← mul_assoc, mul_comm x a, hx, sub_self]
