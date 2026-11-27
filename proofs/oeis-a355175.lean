import OMAStatements.S_oeis_a355175
import Mathlib
open OMA.S_oeis_a355175
open scoped BigOperators Matrix

namespace OMA.P_a355175

theorem psum (n : ℕ) :
    (∑ i ∈ Finset.range n, (i:ℚ)) = n*(n-1)/2 ∧
    (∑ i ∈ Finset.range n, (i:ℚ)^2) = n*(n-1)*(2*n-1)/6 ∧
    (∑ i ∈ Finset.range n, (i:ℚ)^3) = (n*(n-1)/2)^2 ∧
    (∑ i ∈ Finset.range n, (i:ℚ)^4) = n*(n-1)*(2*n-1)*(3*n^2-3*n-1)/30 := by
  induction n with
  | zero => simp
  | succ k ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only [Finset.sum_range_succ, h1, h2, h3, h4]
    push_cast
    refine ⟨by ring, by ring, by ring, by ring⟩

end OMA.P_a355175

theorem OMA.solution : type_of% @OMA.S_oeis_a355175.main := by
  intro n
  let U : Matrix (Fin n) (Fin 3) ℚ := Matrix.of fun i k => ![(i.val:ℚ)^2, 1, (i.val:ℚ)] k
  let V : Matrix (Fin 3) (Fin n) ℚ := Matrix.of fun k j => ![(1:ℚ), (j.val:ℚ)^2, -2*(j.val:ℚ)] k
  have hA : quadraticToeplitz n = 1 + U * V := by
    ext i j
    simp only [quadraticToeplitz, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply,
      Fin.sum_univ_three, U, V]
    simp
    ring
  have key := Matrix.det_one_add_mul_comm U V
  obtain ⟨h1, h2, h3, h4⟩ := OMA.P_a355175.psum n
  have t1 : ∑ x : Fin n, ((x:ℕ):ℚ) = n*(n-1)/2 :=
    (Fin.sum_univ_eq_sum_range (fun i : ℕ => (i:ℚ)) n).trans h1
  have t2 : ∑ x : Fin n, ((x:ℕ):ℚ)^2 = n*(n-1)*(2*n-1)/6 :=
    (Fin.sum_univ_eq_sum_range (fun i : ℕ => (i:ℚ)^2) n).trans h2
  have t2' : ∑ x : Fin n, 2*((x:ℕ):ℚ)*((x:ℕ):ℚ) = 2*(n*(n-1)*(2*n-1)/6) :=
    (Fin.sum_univ_eq_sum_range (fun i : ℕ => 2*(i:ℚ)*i) n).trans
      (by rw [← h2, Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring))
  have t1' : ∑ x : Fin n, 2*((x:ℕ):ℚ) = 2*(n*(n-1)/2) :=
    (Fin.sum_univ_eq_sum_range (fun i : ℕ => 2*(i:ℚ)) n).trans
      (by rw [← h1, Finset.mul_sum])
  have t3 : ∑ x : Fin n, ((x:ℕ):ℚ)^2*((x:ℕ):ℚ) = (n*(n-1)/2)^2 :=
    (Fin.sum_univ_eq_sum_range (fun i : ℕ => (i:ℚ)^2*i) n).trans
      (by rw [← h3]; exact Finset.sum_congr rfl (fun _ _ => by ring))
  have t3' : ∑ x : Fin n, 2*((x:ℕ):ℚ)*((x:ℕ):ℚ)^2 = 2*((n:ℚ)*(n-1)/2)^2 :=
    (Fin.sum_univ_eq_sum_range (fun i : ℕ => 2*(i:ℚ)*i^2) n).trans
      (by rw [← h3, Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring))
  have t4 : ∑ x : Fin n, ((x:ℕ):ℚ)^2*((x:ℕ):ℚ)^2 = (n:ℚ)*(n-1)*(2*n-1)*(3*n^2-3*n-1)/30 :=
    (Fin.sum_univ_eq_sum_range (fun i : ℕ => (i:ℚ)^2*i^2) n).trans
      (by rw [← h4]; exact Finset.sum_congr rfl (fun _ _ => by ring))
  unfold a
  rw [hA, key, Matrix.det_fin_three]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, U, V]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  simp
  rw [t1, t2, t2', t1', t3, t3', t4]
  ring
