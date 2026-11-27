import OMAStatements.S_oeis_a127771

namespace OMA.S_oeis_a127771

open Matrix

variable (N : ℕ)


/-- The 0/1 pattern `[k <= n <= 2k]`, over the integers. -/
def C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℤ := fun i j =>
  if (j : ℕ) ≤ i ∧ (i : ℕ) ≤ 2 * j then 1 else 0

lemma C_det : (C N).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · apply Finset.prod_eq_one
    intro i _
    simp only [C]
    rw [if_pos (by omega)]
  · intro i j hij
    have : (i : ℕ) < j := hij
    simp only [C]
    rw [if_neg (by omega)]

lemma phi_ne_zero (i : Fin (N + 1)) : (((i : ℕ) + 1).totient : ℚ) ≠ 0 := by
  have : 0 < ((i : ℕ) + 1).totient := Nat.totient_pos.2 (by omega)
  exact_mod_cast this.ne'

/-- The candidate inverse `C^-1 * diag(phi(n+1))`. -/
noncomputable def B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ :=
  ((C N)⁻¹).map (Int.castRingHom ℚ) * diagonal (fun i : Fin (N + 1) => (((i : ℕ) + 1).totient : ℚ))

lemma A_eq : A N = diagonal (fun i : Fin (N + 1) => 1 / (((i : ℕ) + 1).totient : ℚ)) *
    (C N).map (Int.castRingHom ℚ) := by
  ext i j
  rw [diagonal_mul]
  simp only [A, C, map_apply]
  split_ifs <;> simp

lemma B_mul_A : B N * A N = 1 := by
  have hu : IsUnit (C N).det := by rw [C_det]; exact isUnit_one
  have hinv : (C N)⁻¹ * C N = 1 := nonsing_inv_mul _ hu
  rw [B, A_eq, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]
  have hd : (diagonal fun i : Fin (N + 1) => (((i : ℕ) + 1).totient : ℚ) * (1 / (((i : ℕ) + 1).totient : ℚ)))
      = 1 := by
    rw [← diagonal_one]
    congr 1
    funext i
    field_simp [phi_ne_zero N i]
  rw [hd, Matrix.one_mul, ← Matrix.map_mul, hinv, Matrix.map_one _ (map_zero _) (map_one _)]

/-- The conjecture: every entry of the inverse triangle (in every truncation) is an integer. -/
theorem integer_entries (i j : Fin (N + 1)) : ∃ z : ℤ, (A N)⁻¹ i j = z := by
  rw [inv_eq_left_inv (B_mul_A N)]
  refine ⟨(C N)⁻¹ i j * (((j : ℕ) + 1).totient : ℤ), ?_⟩
  simp [B, mul_diagonal]

/-- Rows 0..4 of the triangle as listed in the entry. -/
def M5 : Matrix (Fin 5) (Fin 5) ℚ :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, -1, 2, 0, 0; 0, 1, -2, 2, 0; 0, 0, 0, -2, 4]

/-- Control: the listed rows 0..4 are the inverse of the 5 x 5 truncation. -/
example : (A 4)⁻¹ = M5 := by
  apply inv_eq_right_inv
  have t1 : Nat.totient 1 = 1 := by decide
  have t2 : Nat.totient 2 = 1 := by decide
  have t3 : Nat.totient 3 = 2 := by decide
  have t4 : Nat.totient 4 = 2 := by decide
  have t5 : Nat.totient 5 = 4 := by decide
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A, M5, Matrix.mul_apply, Fin.sum_univ_five, t1, t2, t3, t4, t5]

end OMA.S_oeis_a127771

theorem OMA.solution : type_of% @OMA.S_oeis_a127771.main :=
  fun N i j => OMA.S_oeis_a127771.integer_entries N i j
