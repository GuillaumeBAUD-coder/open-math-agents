import FormalConjectures.WrittenOnTheWallII.Test

/-!
# The Cvetković bound for the six-cycle

The adjacency characteristic polynomial has three positive and three negative roots,
counted with multiplicity, and no zero roots.
-/

open Matrix Polynomial SimpleGraph WrittenOnTheWallII.Test

namespace OMA

def cycleSixAdjacency : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 1, 0, 0, 0, 1;
     1, 0, 1, 0, 0, 0;
     0, 1, 0, 1, 0, 0;
     0, 0, 1, 0, 1, 0;
     0, 0, 0, 1, 0, 1;
     1, 0, 0, 0, 1, 0]

theorem cycleSixAdjacency_eq : C6.adjMatrix ℝ = cycleSixAdjacency := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 1500000 in
theorem cycleSix_charpoly : cycleSixAdjacency.charpoly = X ^ 6 - 6 * X ^ 4 + 9 * X ^ 2 - 4 := by
  unfold Matrix.charpoly
  have h : cycleSixAdjacency.charmatrix =
      !![X, -1, 0, 0, 0, -1;
         -1, X, -1, 0, 0, 0;
         0, -1, X, -1, 0, 0;
         0, 0, -1, X, -1, 0;
         0, 0, 0, -1, X, -1;
         -1, 0, 0, 0, -1, (X : ℝ[X])] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cycleSixAdjacency]
  rw [h]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove] <;> ring

theorem cycleSix_roots : (X ^ 6 - 6 * X ^ 4 + 9 * X ^ 2 - 4 : ℝ[X]).roots =
    ({2} + {-2} : Multiset ℝ) + (2 • ({1} : Multiset ℝ) + 2 • ({-1} : Multiset ℝ)) := by
  have h : (X ^ 6 - 6 * X ^ 4 + 9 * X ^ 2 - 4 : ℝ[X]) =
      ((X - C (2 : ℝ)) * (X - C (-2 : ℝ))) *
        ((X - C (1 : ℝ)) ^ 2 * (X - C (-1 : ℝ)) ^ 2) := by
    simp only [map_ofNat, map_one, map_neg]
    ring
  have hab := (monic_X_sub_C (2 : ℝ)).mul (monic_X_sub_C (-2 : ℝ))
  have hcd := ((monic_X_sub_C (1 : ℝ)).pow 2).mul ((monic_X_sub_C (-1 : ℝ)).pow 2)
  rw [h, roots_mul (hab.mul hcd).ne_zero, roots_mul hab.ne_zero, roots_mul hcd.ne_zero]
  simp only [roots_pow, roots_X_sub_C]

end OMA

theorem OMA.solution : type_of% @WrittenOnTheWallII.Test.C6_cvetkovic := by
  unfold SimpleGraph.cvetkovic
  rw [OMA.cycleSixAdjacency_eq, OMA.cycleSix_charpoly, OMA.cycleSix_roots]
  have hs : ∀ a : ℝ, ({a} : Multiset ℝ) = a ::ₘ 0 := fun _ => rfl
  simp only [hs, Multiset.countP_add, Multiset.countP_nsmul, Multiset.countP_cons,
    Multiset.countP_zero]
  norm_num
