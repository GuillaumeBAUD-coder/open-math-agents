import OMAStatements.S_mo_322037
import Mathlib

-- Problem: mo-322037, counterexample n = 7, k = 3, x = (0, 1, 2, 0, 0, 2, 1) / 6.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_322037.main) := by
  intro h
  let f : Fin 7 → ℝ := fun i => if i.1 = 1 ∨ i.1 = 6 then 1 / 6 else if i.1 = 2 ∨ i.1 = 5 then 1 / 3 else 0
  have h1 := h 7 3 (by norm_num) (by norm_num) f
    (fun i => by fin_cases i <;> norm_num [f])
    (by norm_num [Fin.sum_univ_seven, f])
  norm_num [OMA.S_mo_322037.quadratic, Fin.sum_univ_seven, Finset.sum_range_succ, f] at h1
