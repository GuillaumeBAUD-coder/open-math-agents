import OMAStatements.S_oeis_a127711
import Mathlib

open Matrix in
theorem OMA.solution : type_of% @OMA.S_oeis_a127711.main := by
  intro N i j
  let L : Matrix (Fin (N + 1)) (Fin (N + 1)) ℤ := fun i j => if j.val ≤ i.val ∧ i.val ≤ 2 * j.val then 1 else 0
  have e : OMA.S_oeis_a127711.triangle N =
      diagonal (fun i => (Nat.fib (i.val + 1) : ℚ)⁻¹) * L.map (Int.castRingHom ℚ) := by
    ext a b
    simp [OMA.S_oeis_a127711.triangle, L, Matrix.map]
  rw [inv_eq_left_inv (B := (L⁻¹).map (Int.castRingHom ℚ) * diagonal fun i => (Nat.fib (i.val + 1) : ℚ))]
  · simp [mul_diagonal]
    norm_cast
    exact ⟨_, rfl⟩
  rw [e, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]
  have h : (L⁻¹ * L).map (Int.castRingHom ℚ) = 1 := by
    rw [nonsing_inv_mul L]
    · simp
    rw [det_of_isLowerTriangular L fun a b h => if_neg (by simp at h; omega)]
    simp [L, two_mul]
  rw [Matrix.map_mul] at h
  simpa [Nat.fib_eq_zero] using h
