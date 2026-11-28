import FormalConjectures.WrittenOnTheWallII.Test
import Mathlib

/-!
The Petersen graph's Cvetković bound, first formalized by @Genbox in PR #409.
This revision certifies a rational eigenbasis and inverse, then uses characteristic
polynomial identities to count the eigenvalues 3, 1 (five times), and -2 (four times).
The finite matrix identities are proved by ordinary kernel reduction.
-/

open SimpleGraph WrittenOnTheWallII.Test Matrix Polynomial
namespace OMA.Petersen
def vertex : Fin 10 → PetersenVertex := ![⟨{0,1},by decide⟩,⟨{0,2},by decide⟩,⟨{0,3},by decide⟩,⟨{0,4},by decide⟩,⟨{1,2},by decide⟩,⟨{1,3},by decide⟩,⟨{1,4},by decide⟩,⟨{2,3},by decide⟩,⟨{2,4},by decide⟩,⟨{3,4},by decide⟩]
noncomputable def e : Fin 10 ≃ PetersenVertex := Equiv.ofBijective vertex (by decide +kernel)
def P : Matrix (Fin 10) (Fin 10) ℚ := !![1,0,0,1,1,1,0,-1/2,-1/2,-1/2;
    1,1,1,0,0,1,-1,-1/2,1/2,-1/2;
    1,-1,0,-1,0,-1,-1,-1/2,-1/2,1/2;
    1,0,-1,0,-1,-1,-1,-3/2,1/2,1/2;
    1,-1,-1,-1,-1,-1,1,1,0,-1;
    1,1,0,0,0,0,1,1,-1,0;
    1,0,1,0,0,0,1,0,0,0;
    1,0,0,1,0,0,0,1,0,0;
    1,0,0,0,1,0,0,0,1,0;
    1,0,0,0,0,1,0,0,0,1]
def Q : Matrix (Fin 10) (Fin 10) ℚ := !![1/10,1/10,1/10,1/10,1/10,1/10,1/10,1/10,1/10,1/10;
    -1/6,1/6,-1/6,1/6,-1/6,1/2,-1/6,-1/6,1/6,-1/6;
    -1/6,1/6,1/6,-1/6,-1/6,-1/6,1/2,1/6,-1/6,-1/6;
    1/6,-1/6,-1/6,1/6,-1/6,-1/6,1/6,1/2,-1/6,-1/6;
    1/6,-1/6,1/6,-1/6,-1/6,1/6,-1/6,-1/6,1/2,-1/6;
    1/6,1/6,-1/6,-1/6,1/6,-1/6,-1/6,-1/6,-1/6,1/2;
    1/15,-4/15,-4/15,1/15,1/15,1/15,2/5,-4/15,1/15,1/15;
    -4/15,1/15,1/15,-4/15,1/15,1/15,-4/15,2/5,1/15,1/15;
    -4/15,1/15,-4/15,1/15,1/15,-4/15,1/15,1/15,2/5,1/15;
    -4/15,-4/15,1/15,1/15,-4/15,1/15,1/15,1/15,1/15,2/5]
def d : Fin 10 → ℚ := ![3,1,1,1,1,1,-2,-2,-2,-2]
theorem certificate : P * Q = 1 ∧
    ((PetersenGraph.adjMatrix ℚ).submatrix vertex vertex) * P = P * diagonal d := by
  decide +kernel
theorem charpolyQ : ((PetersenGraph.adjMatrix ℚ).submatrix vertex vertex).charpoly =
    (diagonal d).charpoly := by
  calc
    _ = (((PetersenGraph.adjMatrix ℚ).submatrix vertex vertex) * (P*Q)).charpoly := by
      rw [certificate.1, mul_one]
    _ = (P * (diagonal d * Q)).charpoly := by rw [← mul_assoc, certificate.2, mul_assoc]
    _ = ((diagonal d * Q) * P).charpoly := charpoly_mul_comm _ _
    _ = _ := by rw [mul_assoc, mul_eq_one_comm.mp certificate.1, mul_one]

theorem charpolyR : (PetersenGraph.adjMatrix ℝ).charpoly =
    ∏ i : Fin 10, (X - C ((d i : ℚ) : ℝ)) := by
  have hmap : ((PetersenGraph.adjMatrix ℚ).submatrix vertex vertex).map (Rat.castHom ℝ) =
      (PetersenGraph.adjMatrix ℝ).submatrix vertex vertex := by
    ext i j
    simp only [Matrix.map_apply, submatrix_apply, adjMatrix_apply]
    split_ifs <;> simp
  rw [← Matrix.charpoly_reindex e.symm]
  change ((PetersenGraph.adjMatrix ℝ).submatrix vertex vertex).charpoly = _
  rw [← hmap, Matrix.charpoly_map, charpolyQ, Matrix.charpoly_diagonal]
  simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rfl

end OMA.Petersen
open OMA.Petersen

theorem OMA.solution : type_of% @WrittenOnTheWallII.Test.petersen_cvetkovic := by
  unfold cvetkovic
  rw [charpolyR, Polynomial.roots_prod]
  · norm_num [d, Fin.sum_univ_succ, Multiset.countP_add]
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => X_sub_C_ne_zero _)

