import OMAStatements.S_mo_231913
import Mathlib

open OMA.S_mo_231913
open Matrix
open scoped ComplexOrder

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_231913.main) := by
  intro h
  let C : ℤ → Matrix (Fin 1) (Fin 1) ℂ := fun l => Matrix.of fun _ _ => if l = 0 then 2 else -2
  have h0 : (C 0).PosSemidef := by
    have : C 0 = diagonal (fun _ => (2 : ℂ)) := by
      ext i j; fin_cases i; fin_cases j; simp [C]
    rw [this]
    apply PosSemidef.diagonal
    intro i
    simp only [Pi.zero_apply]
    exact_mod_cast (show (0 : ℝ) ≤ 2 by norm_num)
  have hadj : ∀ l : ℤ, C (-l) = (C l)ᴴ := by
    intro l; ext i j
    by_cases hl : l = 0 <;> simp [C, conjTranspose_apply, hl]
  have hnorm : ∀ l : ℤ, -((3 : ℕ) : ℤ) < l → l < (3 : ℕ) → hsNormSq (C l) ≤ hsNormSq (C 0) := by
    intro l _ _
    by_cases hl : l = 0 <;> simp [hsNormSq, C, hl]
  have hM := h 3 1 C h0 hadj hnorm
  have hv := hM.dotProduct_mulVec_nonneg (fun _ => 1)
  simp [dotProduct, mulVec, blockToeplitz, Fintype.sum_prod_type, Fin.sum_univ_three, C] at hv
  norm_num at hv
