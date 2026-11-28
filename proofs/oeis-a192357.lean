import OMAStatements.S_oeis_a192357

namespace OMA.S_oeis_a192357

open Polynomial

lemma q_monic : (X ^ 2 - X - 1 : ℚ[X]).Monic := by monicity!

lemma key (m : ℕ) :
    (X ^ 2 - X - 1 : ℚ[X]) ∣ p (m + 4) - 2 * p (m + 3) - 19 * p (m + 2) + 20 * p (m + 1) + 55 * p m := by
  refine ⟨C (1 / 2) * ((X + C 3) ^ m * (X ^ 2 + 11 * X + 29) +
      (X - C 3) ^ m * (X ^ 2 - 13 * X + 41)), ?_⟩
  have h3 : (C 3 : ℚ[X]) = 3 := map_ofNat C 3
  simp only [p, h3]
  ring

theorem solution_main : ∀ n : ℕ, 4 < n →
    a n = 2 * a (n - 1) + 19 * a (n - 2) - 20 * a (n - 3) - 55 * a (n - 4) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  simp only [a, show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega,
    show m + 4 - 1 = m + 3 by omega, show m + 3 - 1 = m + 2 by omega,
    show m + 2 - 1 = m + 1 by omega, show m + 1 - 1 = m by omega]
  have h0 := (modByMonic_eq_zero_iff_dvd q_monic).2 (key m)
  have hc := congrArg (fun f => f.coeff 0) h0
  simp only [add_modByMonic, sub_modByMonic, coeff_add, coeff_sub, coeff_zero] at hc
  have s2 : ∀ (c : ℚ) (f : ℚ[X]), ((C c * f) %ₘ (X ^ 2 - X - 1)).coeff 0 =
      c * (f %ₘ (X ^ 2 - X - 1)).coeff 0 := by
    intro c f
    rw [← smul_eq_C_mul, smul_modByMonic, coeff_smul, smul_eq_mul]
  have e : ∀ (k : ℕ) (f : ℚ[X]), (k : ℚ[X]) * f = C (k : ℚ) * f := by
    intro k f; simp
  rw [show (2 : ℚ[X]) * p (m + 3) = C 2 * p (m + 3) by rw [show (C 2 : ℚ[X]) = 2 from map_ofNat C 2],
    show (19 : ℚ[X]) * p (m + 2) = C 19 * p (m + 2) by rw [show (C 19 : ℚ[X]) = 19 from map_ofNat C 19],
    show (20 : ℚ[X]) * p (m + 1) = C 20 * p (m + 1) by rw [show (C 20 : ℚ[X]) = 20 from map_ofNat C 20],
    show (55 : ℚ[X]) * p m = C 55 * p m by rw [show (C 55 : ℚ[X]) = 55 from map_ofNat C 55], s2, s2, s2, s2] at hc
  linarith

end OMA.S_oeis_a192357

theorem OMA.solution : type_of% @OMA.S_oeis_a192357.main := OMA.S_oeis_a192357.solution_main
