import OMAStatements.S_mo_200356
import Mathlib

namespace OMA.S_mo_200356

lemma sum_fun2 (f : (Fin 2 → Fin 2) → ℝ) :
    ∑ x, f x = f ![0,0] + f ![0,1] + f ![1,0] + f ![1,1] := by
  rw [← Equiv.sum_comp (piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm f, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  have : ∀ a b : Fin 2, (piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm (a, b) = ![a, b] := by
    intro a b; ext i; fin_cases i <;> rfl
  simp only [this]
  ring

end OMA.S_mo_200356

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_200356.main) := by
  rintro ⟨φ, h⟩
  have h1 := h 2 2 ![1, 0] ![1/2, 1/2] (by simp [OMA.S_mo_200356.IsDist, Fin.forall_fin_two]) (by simp [OMA.S_mo_200356.IsDist, Fin.forall_fin_two]; norm_num)
  have h2 := h 2 2 ![1/4, 3/4] ![3/4, 1/4] (by simp [OMA.S_mo_200356.IsDist, Fin.forall_fin_two]; norm_num) (by simp [OMA.S_mo_200356.IsDist, Fin.forall_fin_two]; norm_num)
  have e1 : OMA.S_mo_200356.tv (![1, 0] : Fin 2 → ℝ) ![1/2, 1/2] = 1/2 := by
    simp [OMA.S_mo_200356.tv, Fin.sum_univ_two]; norm_num
  have e2 : OMA.S_mo_200356.tv (![1/4, 3/4] : Fin 2 → ℝ) ![3/4, 1/4] = 1/2 := by
    simp [OMA.S_mo_200356.tv, Fin.sum_univ_two]; norm_num [abs_of_neg, abs_of_pos]
  have a1 : OMA.S_mo_200356.tv (OMA.S_mo_200356.prodDist 2 (![1, 0] : Fin 2 → ℝ)) (OMA.S_mo_200356.prodDist 2 ![1/2, 1/2]) = 3/4 := by
    simp only [OMA.S_mo_200356.tv, OMA.S_mo_200356.sum_fun2, OMA.S_mo_200356.prodDist, Fin.prod_univ_two]
    simp; norm_num
  have a2 : OMA.S_mo_200356.tv (OMA.S_mo_200356.prodDist 2 (![1/4, 3/4] : Fin 2 → ℝ)) (OMA.S_mo_200356.prodDist 2 ![3/4, 1/4]) = 1/2 := by
    simp only [OMA.S_mo_200356.tv, OMA.S_mo_200356.sum_fun2, OMA.S_mo_200356.prodDist, Fin.prod_univ_two]
    simp; norm_num [abs_of_neg, abs_of_pos]
  rw [e1] at h1
  rw [e2] at h2
  rw [a1] at h1
  rw [a2] at h2
  rw [← h1] at h2
  norm_num at h2
