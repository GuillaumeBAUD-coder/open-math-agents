import OMAStatements.S_mo_473367
import Mathlib

namespace MO473367Aux
def M : Matrix (Fin 3) (Fin 3) ℤ := !![0, -1, 1; -1, 0, 1; 1, 1, 0]
lemma h1 : ∀ i, M i i = 0 := by decide
lemma h2 : ∀ i j, M i j = M j i := by
  intro i j; fin_cases i <;> fin_cases j <;> decide
lemma h3 : ∀ i j, i ≠ j → M i j = -1 ∨ M i j = 1 := by
  intro i j; fin_cases i <;> fin_cases j <;> decide
lemma h4 : ∀ S : Finset (Fin 3), S.Nonempty → S ≠ Finset.univ →
    0 ≤ ∑ i ∈ S, ∑ j ∈ Finset.univ \ S, M i j := by decide
end MO473367Aux

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_473367.main) := by
  intro h
  have key := h 3 MO473367Aux.M MO473367Aux.h1 MO473367Aux.h2 MO473367Aux.h3 MO473367Aux.h4
    ![0, 2, 1]
  simp [OMA.S_mo_473367.quadraticForm, OMA.S_mo_473367.Laplacian, Fin.sum_univ_three,
    Matrix.diagonal, MO473367Aux.M] at key
  norm_num at key
