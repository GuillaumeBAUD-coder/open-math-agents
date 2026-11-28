import OMAStatements.S_mo_349784
import Mathlib

open OMA.S_mo_349784

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_349784.main) := by
  intro h
  have hX : Function.Injective (![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) := by decide
  have hne : ∀ i, ((![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) i).Nonempty := by
    intro i; fin_cases i <;> simp
  have hpd := h (Fin 2) 3 (fun _ => 1) (fun _ => one_pos) _ hX hne
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hpd
  have hv : (![1, 1, -1] : Fin 3 → ℝ) ≠ 0 := by
    intro h0; have := congrFun h0 0; simp at this
  have := hpd.2 hv
  have e : ∀ i j : Fin 3, gram (fun _ : Fin 2 => (1 : ℝ)) ![{0}, {1}, {0, 1}] i j =
      ((![{0}, {1}, {0, 1}] i ∩ ![{0}, {1}, {0, 1}] j : Finset (Fin 2)).card : ℝ) := by
    intro i j; simp [gram]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, e] at this
  simp at this
  norm_num at this
