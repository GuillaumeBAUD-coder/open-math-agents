import OMAReductions.R_wp_gnrs_conjecture_R1
import Mathlib

theorem OMA.solution : OMA.R_wp_gnrs_conjecture_R1.H2 := by
  intro n S cut a ha
  have hmem : ∀ u : Fin n,
      Memℓp (E := fun _ : ℕ => ℝ) (fun i : ℕ => if i ∈ S ∧ cut i u = true then a i else 0) 1 := by
    intro u
    apply memℓp_gen
    apply summable_of_ne_finset_zero (s := S)
    intro i hi
    simp [hi]
  let F : Fin n → lp (fun _ : ℕ => ℝ) 1 := fun u => ⟨_, hmem u⟩
  have hF : ∀ u i, (F u : ∀ _ : ℕ, ℝ) i = if i ∈ S ∧ cut i u = true then a i else 0 :=
    fun _ _ => rfl
  refine ⟨F, fun u v => ?_⟩
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp only [ENNReal.toReal_one, Real.rpow_one, div_one, lp.coeFn_sub, Pi.sub_apply, hF]
  rw [tsum_eq_sum (s := S)]
  · apply Finset.sum_congr rfl
    intro i hi
    have := ha i hi
    cases hu : cut i u <;> cases hv : cut i v <;>
      simp [hi, abs_of_nonneg this]
  · intro i hi
    simp [hi]
