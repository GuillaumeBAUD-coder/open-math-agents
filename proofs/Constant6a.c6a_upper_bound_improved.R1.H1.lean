import OMAReductions.R_Constant6a_c6a_upper_bound_improved_R1
import Mathlib

theorem OMA.solution : OMA.R_Constant6a_c6a_upper_bound_improved_R1.H1 := by
  unfold OMA.R_Constant6a_c6a_upper_bound_improved_R1.H1 Constant6a.C6a
  refine Real.sSup_le (fun c hc => ?_) (by norm_num)
  obtain ⟨i, hi⟩ := hc {∅, {0}} (by decide) (by decide)
  have h1 : (Finset.card ({∅, {0}} : Finset (Finset ℕ)) : ℝ) = 2 := by
    norm_num
  have h2 : (Finset.card (Finset.filter (fun x => i ∈ x) ({∅, {0}} : Finset (Finset ℕ))) : ℝ) ≤ 1 := by
    have : Finset.filter (fun x => i ∈ x) ({∅, {0}} : Finset (Finset ℕ)) ⊆ {{0}} := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with ⟨rfl | rfl, h⟩
      · simp at h
      · rfl
    exact_mod_cast Finset.card_le_card this
  rw [h1] at hi
  linarith
