import FormalConjectures.WrittenOnTheWallII.Test

-- Problem: Testing Graph Invariants — Star5 cvetkovic
-- Upstream: formal-conjectures FormalConjectures/WrittenOnTheWallII/Test.lean:626 (declaration WrittenOnTheWallII.Test.Star5_cvetkovic)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


open Polynomial Matrix SimpleGraph WrittenOnTheWallII.Test

namespace OMA

def M6 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 1, 1, 1, 1, 1;
     1, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0]

lemma adj_eq : Star5.adjMatrix ℝ = Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm M6 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [M6, adjMatrix_apply] <;> rfl

lemma M6_charpoly : M6.charpoly = X ^ 6 - 5 * X ^ 4 := by
  unfold Matrix.charpoly
  have h : M6.charmatrix =
      !![X, -1, -1, -1, -1, -1;
         -1, X, 0, 0, 0, 0;
         -1, 0, X, 0, 0, 0;
         -1, 0, 0, X, 0, 0;
         -1, 0, 0, 0, X, 0;
         -1, 0, 0, 0, 0, (X : ℝ[X])] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M6]
  rw [h]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

lemma factor : (X ^ 6 - 5 * X ^ 4 : ℝ[X]) =
    X ^ 4 * ((X - C (Real.sqrt 5)) * (X - C (-Real.sqrt 5))) := by
  have h : (C (Real.sqrt 5) : ℝ[X]) ^ 2 = 5 := by
    rw [← C_pow, Real.sq_sqrt (by norm_num)]
    rfl
  rw [C_neg]
  linear_combination (X ^ 4 : ℝ[X]) * h

lemma roots_eq : (X ^ 6 - 5 * X ^ 4 : ℝ[X]).roots =
    4 • ({0} : Multiset ℝ) + ({Real.sqrt 5} + {-Real.sqrt 5}) := by
  have hne : (X ^ 4 * ((X - C (Real.sqrt 5)) * (X - C (-Real.sqrt 5))) : ℝ[X]) ≠ 0 :=
    ((monic_X_pow 4).mul ((monic_X_sub_C _).mul (monic_X_sub_C _))).ne_zero
  rw [factor, roots_mul hne, roots_mul (right_ne_zero_of_mul hne), roots_pow, roots_X,
    roots_X_sub_C, roots_X_sub_C]

end OMA

theorem OMA.solution : type_of% @WrittenOnTheWallII.Test.Star5_cvetkovic := by
  have hr : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  unfold cvetkovic
  rw [OMA.adj_eq, Matrix.charpoly_reindex, OMA.M6_charpoly, OMA.roots_eq]
  have hs : ∀ a : ℝ, ({a} : Multiset ℝ) = a ::ₘ 0 := fun _ => rfl
  simp only [hs, Multiset.countP_add, Multiset.countP_nsmul, Multiset.countP_cons,
    Multiset.countP_zero]
  simp [hr, hr.ne, hr.ne', not_lt.mpr hr.le]
