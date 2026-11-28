import OMAStatements.S_mo_473367
import Mathlib

/-!
MathOverflow 473367: the signed triangle with edges `01`, `02` positive and `12` negative
(David Roberson's answer) satisfies every cut condition, but its Laplacian has
`xᵀ L x = -2 < 0` at `x = (0, 1, -1)`.
-/

namespace OMA.P473367

open Finset Matrix OMA.S_mo_473367

/-- A signed triangle: edges `01`, `02` positive, edge `12` negative. -/
def A : Matrix (Fin 3) (Fin 3) ℤ := !![0, 1, 1; 1, 0, -1; 1, -1, 0]

lemma cut : ∀ S : Finset (Fin 3), S.Nonempty → S ≠ univ →
    0 ≤ ∑ i ∈ S, ∑ j ∈ univ \ S, A i j := by decide

lemma symm : ∀ i j, A i j = A j i := by
  intro i j; fin_cases i <;> fin_cases j <;> rfl

lemma pm : ∀ i j, i ≠ j → A i j = -1 ∨ A i j = 1 := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [A]

lemma neg : quadraticForm A ![0, 1, -1] = -2 := by
  simp [quadraticForm, S_mo_473367.Laplacian, A, Fin.sum_univ_three, Matrix.sub_apply,
    Matrix.diagonal_apply]
  norm_num

theorem disproof_aux : ¬ ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ),
    (∀ i, A i i = 0) → (∀ i j, A i j = A j i) →
    (∀ i j, i ≠ j → A i j = -1 ∨ A i j = 1) →
    (∀ S : Finset (Fin n), S.Nonempty → S ≠ univ →
      0 ≤ ∑ i ∈ S, ∑ j ∈ univ \ S, A i j) →
    ∀ x : Fin n → ℝ, 0 ≤ quadraticForm A x := by
  intro h
  have := h 3 A (by decide) symm pm cut ![0, 1, -1]
  rw [neg] at this
  norm_num at this

end OMA.P473367

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_473367.main) := OMA.P473367.disproof_aux
