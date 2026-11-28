import OMAStatements.S_mo_269499
import Mathlib

open Matrix

namespace OMA.S_mo_269499

noncomputable def P0 : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 1/2, 1/2; 0, 1/2, 1/2]
noncomputable def Y0 : Matrix (Fin 2) (Fin 3) ℝ := !![-1, 1, 1; 1, -1/2, -1/2]
def x0 : Fin 3 → ℝ := ![2, 1, 1]

theorem aux : ¬ (∀ (k : ℕ) (x : Fin k → ℝ), (∀ i, 0 < x i) →
    ∀ P : Matrix (Fin k) (Fin k) ℝ, Pᵀ = P → P * P = P →
      P * designMatrix x = designMatrix x →
      (∃ Y : Matrix (Fin 2) (Fin k) ℝ, P = designMatrix x * Y) →
      ∀ d₁ d₂ d₃ : Fin k → ℝ, (∀ i, 0 < d₁ i) → (∀ i, 0 < d₂ i) → (∀ i, 0 < d₃ i) →
        ∀ j : Fin 2,
          ((designMatrix x)ᵀ * diagonal d₁ * diagonal d₂ * diagonal d₃ * designMatrix x) j j ≤
            ((designMatrix x)ᵀ * diagonal d₁ * P * diagonal d₂ * Pᵀ * diagonal d₃ *
              designMatrix x) j j) := by
  intro h
  have hx : ∀ i, 0 < x0 i := by
    intro i; fin_cases i <;> simp [x0]
  have h1 : P0ᵀ = P0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [P0]
  have h2 : P0 * P0 = P0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [P0, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
  have h3 : P0 * designMatrix x0 = designMatrix x0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [P0, designMatrix, x0, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
  have h4 : ∃ Y : Matrix (Fin 2) (Fin 3) ℝ, P0 = designMatrix x0 * Y := by
    refine ⟨Y0, ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [P0, Y0, designMatrix, x0, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
  have key := h 3 x0 hx P0 h1 h2 h3 h4 ![1,1,2] ![1,1,1] ![1,1,2]
    (by intro i; fin_cases i <;> simp) (by intro i; fin_cases i <;> simp)
    (by intro i; fin_cases i <;> simp) 0
  simp [P0, designMatrix, x0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal_apply, Matrix.transpose_apply] at key
  norm_num at key

end OMA.S_mo_269499

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_269499.main) := OMA.S_mo_269499.aux
