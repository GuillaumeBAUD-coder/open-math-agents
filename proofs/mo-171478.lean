import OMAStatements.S_mo_171478
import Mathlib

theorem OMA.solution : type_of% @OMA.S_mo_171478.main := by
  refine ⟨ℝ, inferInstance, ?_⟩
  refine ⟨inferInstance, ?_⟩
  refine ⟨inferInstance, fun _ => 0, ?_, ?_, ?_, ?_, ?_⟩
  · unfold OMA.S_mo_171478.boundedOnBalls
    intro R
    exact ⟨0, fun x _ => by simp⟩
  · exact continuous_const
  · intro x y
    simp
  · unfold OMA.S_mo_171478.coercive
    intro h
    obtain ⟨R, hR⟩ := h 1
    have h2 : R ≤ |R| := le_abs_self R
    have h3 := le_abs_self (|R| + 1)
    have h1 := hR (|R| + 1) (by
      rw [Real.norm_eq_abs]
      linarith)
    simp at h1
    linarith
  · intro h
    obtain ⟨x, hx⟩ := h 1
    simp at hx
