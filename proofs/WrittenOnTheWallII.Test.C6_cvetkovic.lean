import FormalConjectures.WrittenOnTheWallII.Test

-- Problem: Testing Graph Invariants — C6 cvetkovic
-- Upstream: formal-conjectures FormalConjectures/WrittenOnTheWallII/Test.lean:491 (declaration WrittenOnTheWallII.Test.C6_cvetkovic)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


open Polynomial Matrix SimpleGraph WrittenOnTheWallII.Test

namespace OMA

def M6 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 1, 0, 0, 0, 1;
     1, 0, 1, 0, 0, 0;
     0, 1, 0, 1, 0, 0;
     0, 0, 1, 0, 1, 0;
     0, 0, 0, 1, 0, 1;
     1, 0, 0, 0, 1, 0]

lemma adj_eq : C6.adjMatrix ℝ = M6 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M6, adjMatrix_apply, cycleGraph_adj] <;> decide

lemma M6_charpoly : M6.charpoly = (X ^ 2 - 4) * (X ^ 2 - 1) ^ 2 := by
  unfold Matrix.charpoly
  have h : M6.charmatrix =
      !![X, -1, 0, 0, 0, -1;
         -1, X, -1, 0, 0, 0;
         0, -1, X, -1, 0, 0;
         0, 0, -1, X, -1, 0;
         0, 0, 0, -1, X, -1;
         -1, 0, 0, 0, -1, (X : ℝ[X])] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M6]
  rw [h]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

lemma factor : ((X ^ 2 - 4) * (X ^ 2 - 1) ^ 2 : ℝ[X]) =
    ((X - C 2) * (X - C (-2))) * ((X - C 1) * (X - C (-1))) ^ 2 := by
  simp only [C_neg, map_ofNat, C_1]
  ring

lemma roots_eq : ((X ^ 2 - 4) * (X ^ 2 - 1) ^ 2 : ℝ[X]).roots =
    ({2} + {-2}) + 2 • ({1} + {-1}) := by
  rw [factor]
  have h1 : ((X - C 2) * (X - C (-2)) : ℝ[X]) ≠ 0 :=
    ((monic_X_sub_C _).mul (monic_X_sub_C _)).ne_zero
  have h2 : (((X - C 1) * (X - C (-1))) ^ 2 : ℝ[X]) ≠ 0 :=
    (((monic_X_sub_C _).mul (monic_X_sub_C _)).pow 2).ne_zero
  rw [roots_mul (mul_ne_zero h1 h2), roots_pow, roots_mul h1,
    roots_mul (((monic_X_sub_C _).mul (monic_X_sub_C _)).ne_zero),
    roots_X_sub_C, roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]

end OMA

theorem OMA.solution : type_of% @WrittenOnTheWallII.Test.C6_cvetkovic := by
  unfold cvetkovic
  rw [OMA.adj_eq, OMA.M6_charpoly, OMA.roots_eq]
  have hs : ∀ a : ℝ, ({a} : Multiset ℝ) = a ::ₘ 0 := fun _ => rfl
  simp only [hs, Multiset.countP_add, Multiset.countP_nsmul, Multiset.countP_cons,
    Multiset.countP_zero]
  norm_num
