import OMAStatements.S_arxiv_2202_11520
import Mathlib

/- Original Lean disproof by Volkopat in upstream PR #35899.
   This revision uses matrix notation for the same counterexample. -/

namespace OMA.P_arxiv_2202_11520

open OMA.S_arxiv_2202_11520

private def A_int : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, -3, 1; 0, -1, 0; 3, -10, 1]

private def B_int : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, -1; 4, -2, 10; 2, 1, 7]

private def C_int : Matrix (Fin 3) (Fin 3) ℤ :=
  A_int * B_int - (2 : ℤ) • (B_int * A_int)

def A_cx : Matrix (Fin 3) (Fin 3) ℂ := A_int.map (Int.cast : ℤ → ℂ)
def B_cx : Matrix (Fin 3) (Fin 3) ℂ := B_int.map (Int.cast : ℤ → ℂ)

private lemma frobNormSq_map_int (M : Matrix (Fin 3) (Fin 3) ℤ) :
    frobNormSq (M.map (Int.cast : ℤ → ℂ)) =
      ((∑ i : Fin 3, ∑ j : Fin 3, M i j * M i j : ℤ) : ℝ) := by
  unfold frobNormSq
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.map_apply, Complex.norm_intCast, sq_abs]
  ring

private lemma qComm_eq_map : qComm 2 A_cx B_cx = C_int.map (Int.cast : ℤ → ℂ) := by
  ext i j
  simp only [qComm, A_cx, B_cx, C_int, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.map_apply, smul_eq_mul, Fin.sum_univ_three]
  push_cast
  ring

lemma trace_A_cx : Matrix.trace A_cx = 0 := by
  have diag : A_int 0 0 = 0 ∧ A_int 1 1 = -1 ∧ A_int 2 2 = 1 := by decide
  simp [Matrix.trace, Matrix.diag, A_cx, Fin.sum_univ_three, diag.1, diag.2.1, diag.2.2]

private lemma frob_ineq_int :
    (5 : ℤ) * (∑ i : Fin 3, ∑ j : Fin 3, A_int i j * A_int i j) *
        (∑ i : Fin 3, ∑ j : Fin 3, B_int i j * B_int i j) <
      ∑ i : Fin 3, ∑ j : Fin 3, C_int i j * C_int i j := by
  decide

lemma qComm_beats_bound :
    (1 + (2 : ℝ) ^ 2) * frobNormSq A_cx * frobNormSq B_cx < frobNormSq (qComm 2 A_cx B_cx) := by
  rw [qComm_eq_map, A_cx, B_cx, frobNormSq_map_int, frobNormSq_map_int, frobNormSq_map_int]
  have h5 : (1 + (2 : ℝ) ^ 2) = ((5 : ℤ) : ℝ) := by norm_num
  rw [h5]
  exact_mod_cast frob_ineq_int

end OMA.P_arxiv_2202_11520

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2202_11520.main) := by
  intro h
  have hle := h 3 (by norm_num) 2 (by norm_num)
    OMA.P_arxiv_2202_11520.A_cx OMA.P_arxiv_2202_11520.B_cx
    (Or.inl OMA.P_arxiv_2202_11520.trace_A_cx)
  linarith [OMA.P_arxiv_2202_11520.qComm_beats_bound]
