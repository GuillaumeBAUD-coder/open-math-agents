import OMAStatements.S_mo_171478
import Mathlib

/-!
MathOverflow 171478: the zero map on `ℝ` is bounded on balls, continuous and monotone, but it is
neither coercive nor surjective, so coercivity cannot be dropped from Minty's theorem.
-/

namespace OMA.P171478

open OMA.S_mo_171478

theorem proof_aux : ∃ (H : Type) (normed : NormedAddCommGroup H),
    letI := normed
    ∃ innerSpace : InnerProductSpace ℝ H,
    letI := innerSpace
    ∃ _ : CompleteSpace H, ∃ f : H → H,
      boundedOnBalls f ∧ Continuous f ∧
      (∀ x y, 0 ≤ inner ℝ (f x - f y) (x - y)) ∧ ¬ coercive f ∧ ¬ Function.Surjective f := by
  refine ⟨ℝ, inferInstance, inferInstance, inferInstance, fun _ => 0, ?_, continuous_const,
    fun x y => by simp, ?_, ?_⟩
  · exact fun R => ⟨0, fun x _ => by simp⟩
  · intro h
    obtain ⟨R, hR⟩ := h 1
    have := hR (max R 1) (by rw [Real.norm_eq_abs, abs_of_pos (by positivity)]; exact le_max_left _ _)
    simp at this; linarith
  · intro h
    obtain ⟨x, hx⟩ := h 1
    simp at hx

end OMA.P171478

theorem OMA.solution : type_of% @OMA.S_mo_171478.main := OMA.P171478.proof_aux
