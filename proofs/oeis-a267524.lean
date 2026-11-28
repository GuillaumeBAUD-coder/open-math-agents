import OMAStatements.S_oeis_a267524

namespace OMA.A267524Proof
open OMA.S_oeis_a267524 PowerSeries

def P (t : ℕ) (x : ℤ) : Bool :=
  if t = 0 then (if x = 0 then true else false) else (if x = 2 - t ∨ x = 1 - t then false else true)

theorem S (t : ℕ) : ∀ x, state 139 t x = P t x := by
  induction t with
  | zero => intro x; simp [state, P]
  | succ t ih =>
    intro x
    simp only [state, step, ih, P]
    push_cast
    split_ifs <;> first | rfl | (exfalso; omega)

theorem cv (n : ℕ) : c n = if n = 1 ∨ n = 2 then 0 else 1 := by
  simp only [c, S, P]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem U (n : ℕ) : a (n + 1) = 10 * a n + c (n + 1) := by
  simp only [a]
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [show n + 1 - k = n - k + 1 by simp at hk; omega, pow_succ]
  ring

theorem R (n : ℕ) (hn : 3 < n) : (a n : ℤ) = 11 * a (n - 1) - 10 * a (n - 2) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 4 := ⟨n - 4, by omega⟩
  have h1 : a (p + 4) = 10 * a (p + 3) + 1 := by rw [U, cv, if_neg (by omega)]
  have h2 : a (p + 3) = 10 * a (p + 2) + 1 := by rw [U, cv, if_neg (by omega)]
  rw [show p + 4 - 1 = p + 3 by omega, show p + 4 - 2 = p + 2 by omega]
  omega

theorem G : A = (1 - X + X ^ 3) * ((1 - X) * (1 - 10 * X))⁻¹ := by
  have hd : constantCoeff (((1 - X) * (1 - 10 * X)) : ℚ⟦X⟧) ≠ 0 := by simp
  have k : A * ((1 - X) * (1 - 10 * X)) = 1 - X + X ^ 3 := by
    rw [show A * ((1 - X) * (1 - 10 * X)) = C (1 : ℚ) * A + C (-11 : ℚ) * (A * X ^ 1) + C (10 : ℚ) * (A * X ^ 2) by
        simp only [map_neg, map_ofNat, map_one]; ring,
      show (1 - X + X ^ 3 : ℚ⟦X⟧) = C (1 : ℚ) + C (-1 : ℚ) * X ^ 1 + C (1 : ℚ) * X ^ 3 by
        simp only [map_neg, map_one]; ring]
    ext n
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, A, coeff_C]
    have v : ∀ n, a (n + 1) = 10 * a n + c (n + 1) := U
    rcases Nat.lt_or_ge n 4 with hn | hn
    · have a0 : a 0 = 1 := rfl
      interval_cases n <;> norm_num [v, cv, a0]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have h := R (m + 4) (by omega)
      simp only [show 1 ≤ m + 4 by omega, show 2 ≤ m + 4 by omega, show 3 ≤ m + 4 by omega, show m + 4 ≠ 0 by omega,
        show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 3 ≠ 0 by omega,
        show m + 4 - 3 ≠ 0 by omega, ↓reduceIte] at h ⊢
      have h' : ((a (m + 4) : ℤ) : ℚ) = 11 * ((a (m + 3) : ℤ) : ℚ) - 10 * ((a (m + 2) : ℤ) : ℚ) := by exact_mod_cast h
      push_cast at h'
      linear_combination h'
  rw [← k, mul_assoc, PowerSeries.mul_inv_cancel _ hd, mul_one]

end OMA.A267524Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a267524.main := ⟨OMA.A267524Proof.R, OMA.A267524Proof.G⟩
