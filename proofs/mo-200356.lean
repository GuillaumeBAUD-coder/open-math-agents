import OMAStatements.S_mo_200356
import Mathlib

/-!
MathOverflow 200356: following the answer of Aryeh Kontorovich, take `P = (0, 1)`,
`P' = (1/5, 4/5)` and `Q = (1/10, 9/10)`. Both pairs have total variation distance `1/10`, but
the two-sample products have total variation distances `19/100` and `17/100`.
-/

namespace OMA.P200356

open OMA.S_mo_200356

lemma sum_two_two (f : (Fin 2 → Fin 2) → ℝ) :
    ∑ x, f x = f ![0, 0] + f ![0, 1] + f ![1, 0] + f ![1, 1] := by
  rw [← (piFinTwoEquiv fun _ => Fin 2).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, piFinTwoEquiv_symm_apply]
  ring_nf
  rfl

lemma tv2 (P Q : Fin 2 → ℝ) :
    tv (prodDist 2 P) (prodDist 2 Q) =
      (|P 0 * P 0 - Q 0 * Q 0| + |P 0 * P 1 - Q 0 * Q 1| + |P 1 * P 0 - Q 1 * Q 0| +
        |P 1 * P 1 - Q 1 * Q 1|) / 2 := by
  simp only [tv, prodDist, sum_two_two, Fin.prod_univ_two]
  simp

lemma disproof_aux : ¬ (∃ φ : ℕ → ℕ → ℝ → ℝ, ∀ (k n : ℕ) (P Q : Fin k → ℝ), IsDist P → IsDist Q →
      tv (prodDist n P) (prodDist n Q) = φ k n (tv P Q)) := by
  rintro ⟨φ, hφ⟩
  have hP : IsDist (![0, 1] : Fin 2 → ℝ) := ⟨by intro i; fin_cases i <;> simp, by simp⟩
  have hP' : IsDist (![1/5, 4/5] : Fin 2 → ℝ) :=
    ⟨by intro i; fin_cases i <;> norm_num, by simp [Fin.sum_univ_two]; norm_num⟩
  have hQ : IsDist (![1/10, 9/10] : Fin 2 → ℝ) :=
    ⟨by intro i; fin_cases i <;> norm_num, by simp [Fin.sum_univ_two]; norm_num⟩
  have h1 := hφ 2 2 _ _ hP hQ
  have h2 := hφ 2 2 _ _ hP' hQ
  have e1 : tv (![0, 1] : Fin 2 → ℝ) ![1/10, 9/10] = 1 / 10 := by
    simp [tv, Fin.sum_univ_two]; norm_num [abs_of_neg, abs_of_pos]
  have e2 : tv (![1/5, 4/5] : Fin 2 → ℝ) ![1/10, 9/10] = 1 / 10 := by
    simp [tv, Fin.sum_univ_two]; norm_num [abs_of_neg, abs_of_pos]
  rw [e1] at h1; rw [e2] at h2
  rw [tv2] at h1 h2
  simp at h1 h2
  norm_num [abs_of_neg, abs_of_pos] at h1 h2
  linarith

end OMA.P200356

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_200356.main) := OMA.P200356.disproof_aux
