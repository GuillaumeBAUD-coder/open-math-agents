import OMAStatements.S_mo_322037
import Mathlib

-- Problem: mo-322037, is the cyclic quadratic form sum_i sum_{j<k} x_i x_{i+j} minimized over
-- the probability simplex at the uniform vector?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. For n = 7 and k = 3 the uniform vector gives 3/7, while x = (0, 1, 2, 0, 0, 2, 1) / 6
-- gives 15/36 = 5/12 < 3/7.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_322037.main) := by
  intro h
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ, f = fun m =>
      if m = 1 ∨ m = 6 then (1 / 6 : ℝ) else if m = 2 ∨ m = 5 then 1 / 3 else 0 := ⟨_, rfl⟩
  have hnonneg : ∀ i : Fin 7, 0 ≤ f i.val := by
    intro i
    rw [hf]
    dsimp only
    split_ifs <;> norm_num
  have hsum : ∑ i : Fin 7, f i.val = 1 := by
    norm_num [Fin.sum_univ_seven, hf]
  have h1 := h 7 3 (by norm_num) (by norm_num) (fun i => f i.val) hnonneg hsum
  have e1 : OMA.S_mo_322037.quadratic 3 (fun _ : Fin 7 => 1 / ((7 : ℕ) : ℝ)) = 3 / 7 := by
    norm_num [OMA.S_mo_322037.quadratic]
  have e2 : OMA.S_mo_322037.quadratic 3 (fun i : Fin 7 => f i.val) = 5 / 12 := by
    norm_num [OMA.S_mo_322037.quadratic, Fin.sum_univ_seven, Finset.sum_range_succ, hf]
  rw [e1, e2] at h1
  norm_num at h1
