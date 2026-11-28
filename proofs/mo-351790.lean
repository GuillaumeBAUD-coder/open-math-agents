import OMAStatements.S_mo_351790
import Mathlib

open OMA.S_mo_351790
open Matrix

noncomputable def mo351790_s : ℝ := Real.sqrt 2 / 2

lemma mo351790_s_sq : mo351790_s * mo351790_s = 1 / 2 := by
  unfold mo351790_s
  have h := Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  linear_combination h / 4

lemma mo351790_s_pos : 0 < mo351790_s := by
  unfold mo351790_s; positivity

noncomputable def mo351790_Q2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-mo351790_s, mo351790_s; mo351790_s, mo351790_s]

lemma mo351790_Q2_orth : mo351790_Q2ᵀ * mo351790_Q2 = 1 := by
  have h := mo351790_s_sq
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [mo351790_Q2, Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

lemma mo351790_Q2_det : mo351790_Q2.det = -1 := by
  have h := mo351790_s_sq
  rw [Matrix.det_fin_two]
  simp [mo351790_Q2]
  linarith

lemma mo351790_Q2_abs (i j : Fin 2) : |mo351790_Q2 i j| = mo351790_s := by
  have h := mo351790_s_pos
  fin_cases i <;> fin_cases j <;> simp [mo351790_Q2, abs_of_pos h]

lemma mo351790_Q2_last (i : Fin 2) : mo351790_Q2 i 1 = mo351790_s ∧ mo351790_Q2 1 i = mo351790_s := by
  fin_cases i <;> simp [mo351790_Q2]

noncomputable def mo351790_K : Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℝ :=
  Matrix.kronecker mo351790_Q2 (Matrix.kronecker mo351790_Q2 mo351790_Q2)

lemma mo351790_orth_kron {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix n n ℝ) (hA : Aᵀ * A = 1) (hB : Bᵀ * B = 1) :
    (Matrix.kronecker A B)ᵀ * (Matrix.kronecker A B) = 1 := by
  unfold Matrix.kronecker
  rw [← Matrix.kroneckerMap_transpose, ← Matrix.mul_kronecker_mul, hA, hB, Matrix.one_kronecker_one]

lemma mo351790_K_orth : mo351790_Kᵀ * mo351790_K = 1 :=
  mo351790_orth_kron _ _ mo351790_Q2_orth (mo351790_orth_kron _ _ mo351790_Q2_orth mo351790_Q2_orth)

lemma mo351790_K_det : mo351790_K.det = 1 := by
  unfold mo351790_K Matrix.kronecker
  rw [Matrix.det_kronecker, Matrix.det_kronecker, mo351790_Q2_det]
  norm_num

def mo351790_e : Fin 2 × (Fin 2 × Fin 2) ≃ Fin 8 :=
  (Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans finProdFinEquiv

theorem OMA.solution : type_of% @OMA.S_mo_351790.main := by
  refine ⟨Matrix.reindex mo351790_e mo351790_e mo351790_K, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.transpose_reindex, Matrix.reindex_apply, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv, mo351790_K_orth,
      Matrix.submatrix_one_equiv]
  · rw [Matrix.det_reindex_self, mo351790_K_det]
  · intro i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, mo351790_K,
      Matrix.kronecker, Matrix.kroneckerMap_apply, abs_mul, mo351790_Q2_abs]
  · intro i
    have h7 : mo351790_e.symm 7 = (1, (1, 1)) := by decide
    have hs := mo351790_s_pos
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, h7, mo351790_K,
      Matrix.kronecker, Matrix.kroneckerMap_apply, (mo351790_Q2_last _).1, (mo351790_Q2_last _).2]
    constructor <;> positivity
