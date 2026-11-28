import OMAStatements.S_oeis_a127755
import Mathlib

namespace IntegralTriangleInverse

open Matrix OMA.S_oeis_a127755

private theorem inverse_entries (N : ℕ) (i j : Fin (N + 1)) :
    ∃ z : ℤ, (triangle N)⁻¹ i j = (z : ℚ) := by
  let U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℤ := fun a b =>
    if b.val ≤ a.val ∧ a.val ≤ 2 * b.val then 1 else 0
  let fact (a : Fin (N + 1)) : ℤ := a.val.factorial
  let D := diagonal fact
  let E : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ :=
    diagonal (fun a => ((a.val.factorial : ℚ))⁻¹)
  let cast : ℤ →+* ℚ := Int.castRingHom ℚ
  let J := U⁻¹ * D
  have htri : U.IsLowerTriangular := by
    intro a b hab
    have hlt : a.val < b.val := hab
    change (if b.val ≤ a.val ∧ a.val ≤ 2 * b.val then (1 : ℤ) else 0) = 0
    exact if_neg (fun h => (Nat.not_le.mpr hlt) h.1)
  have hdet : U.det = 1 := by
    rw [det_of_isLowerTriangular _ htri]
    have hd (a : Fin (N + 1)) : U a a = 1 := by
      have h : a.val ≤ 2 * a.val := by omega
      simp [U, h]
    simp [hd]
  have hU : U * U⁻¹ = 1 := mul_nonsing_inv U (by rw [hdet]; exact isUnit_one)
  have hcast : U.map cast * U⁻¹.map cast = 1 := by
    rw [← Matrix.map_mul, hU, Matrix.map_one cast (map_zero _) (map_one _)]
  have hD : D.map cast = diagonal (fun a : Fin (N + 1) => (a.val.factorial : ℚ)) := by
    ext a b
    by_cases h : a = b
    · subst b
      simp [D, fact, cast]
    · simp [D, cast, h]
  have hE : E * D.map cast = 1 := by
    rw [hD]
    change diagonal (fun a : Fin (N + 1) => ((a.val.factorial : ℚ))⁻¹) * _ = 1
    rw [diagonal_mul_diagonal]
    have hf (a : Fin (N + 1)) : (a.val.factorial : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_ne_zero a.val)
    simp [hf]
  have hfactor : triangle N = E * U.map cast := by
    ext a b
    change triangle N a b =
      (diagonal (fun c : Fin (N + 1) => ((c.val.factorial : ℚ))⁻¹) * U.map cast) a b
    rw [diagonal_mul]
    change (if b.val ≤ a.val ∧ a.val ≤ 2 * b.val
      then (a.val.factorial : ℚ)⁻¹ else 0) =
      (a.val.factorial : ℚ)⁻¹ * cast
        (if b.val ≤ a.val ∧ a.val ≤ 2 * b.val then 1 else 0)
    by_cases h : b.val ≤ a.val ∧ a.val ≤ 2 * b.val
    · rw [if_pos h, if_pos h, map_one, mul_one]
    · rw [if_neg h, if_neg h, map_zero, mul_zero]
  have hJ : triangle N * J.map cast = 1 := by
    change triangle N * (U⁻¹ * D).map cast = 1
    rw [hfactor, Matrix.map_mul]
    calc
      (E * U.map cast) * (U⁻¹.map cast * D.map cast) =
          (E * (U.map cast * U⁻¹.map cast)) * D.map cast := by simp [mul_assoc]
      _ = 1 := by rw [hcast, mul_one, hE]
  have hi : (triangle N)⁻¹ = J.map cast := by
    calc
      (triangle N)⁻¹ = (triangle N)⁻¹ * (triangle N * J.map cast) := by rw [hJ, mul_one]
      _ = J.map cast :=
        nonsing_inv_mul_cancel_left _ _ (isUnit_det_of_right_inverse hJ)
  exact ⟨J i j, congrFun (congrFun hi i) j⟩

end IntegralTriangleInverse

theorem OMA.solution : type_of% @OMA.S_oeis_a127755.main :=
  IntegralTriangleInverse.inverse_entries