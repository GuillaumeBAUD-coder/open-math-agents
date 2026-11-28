import OMAStatements.S_oeis_a025249

namespace OMA.P025249

open PowerSeries

/-- The sequence `s` with the value at 0 replaced by 0. -/
def t (s : ℕ → ℤ) (n : ℕ) : ℤ := if n = 0 then 0 else s n

lemma t_zero (s : ℕ → ℤ) : t s 0 = 0 := by
  simp [t]

lemma t_succ (s : ℕ → ℤ) (n : ℕ) : t s (n + 1) = s (n + 1) := by
  simp [t]

lemma sum_Icc_range (f : ℕ → ℤ) (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 m, f k = ∑ k ∈ Finset.range m, f (k + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- The coefficients of index at least 4 of the square of the generating function. -/
lemma conv (s : ℕ → ℤ) (h1 : s 1 = 1) (h2 : s 2 = 0)
    (hrec : ∀ n : ℕ, 4 ≤ n → s n = ∑ k ∈ Finset.Icc 1 (n - 3), s k * s (n - k)) (m : ℕ) :
    coeff (m + 4) (PowerSeries.mk (t s) * PowerSeries.mk (t s)) = s (m + 4) + s (m + 3) := by
  have e1 : m + 4 - 3 = m + 1 := by omega
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ',
    hrec (m + 4) (by omega), sum_Icc_range, e1]
  have hs : ∀ k ∈ Finset.range (m + 1),
      coeff (k + 1) (PowerSeries.mk (t s)) * coeff (m + 4 - (k + 1)) (PowerSeries.mk (t s))
        = s (k + 1) * s (m + 4 - (k + 1)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    obtain ⟨j, hj⟩ : ∃ j, m + 4 - (k + 1) = j + 1 := ⟨m + 4 - (k + 1) - 1, by omega⟩
    rw [hj, coeff_mk, coeff_mk, t_succ, t_succ]
  rw [Finset.sum_congr rfl hs]
  have a0 : coeff 0 (PowerSeries.mk (t s)) = 0 := by
    rw [coeff_mk, t_zero]
  have a1 : coeff (m + 4 - (m + 3)) (PowerSeries.mk (t s)) = 1 := by
    rw [show m + 4 - (m + 3) = 0 + 1 by omega, coeff_mk, t_succ]
    exact h1
  have a2 : coeff (m + 4 - (m + 2)) (PowerSeries.mk (t s)) = 0 := by
    rw [show m + 4 - (m + 2) = 1 + 1 by omega, coeff_mk, t_succ]
    exact h2
  have a3 : coeff (m + 4 - (m + 4)) (PowerSeries.mk (t s)) = 0 := by
    rw [Nat.sub_self, coeff_mk, t_zero]
  have a4 : coeff (m + 3) (PowerSeries.mk (t s)) = s (m + 3) := by
    rw [coeff_mk, t_succ]
  rw [a0, a1, a2, a3, a4]
  ring

/-- The quadratic equation for the generating function. -/
lemma quad (s : ℕ → ℤ) (h1 : s 1 = 1) (h2 : s 2 = 0) (h3 : s 3 = 2)
    (hrec : ∀ n : ℕ, 4 ≤ n → s n = ∑ k ∈ Finset.Icc 1 (n - 3), s k * s (n - k)) :
    (PowerSeries.mk (t s) : ℤ⟦X⟧) * PowerSeries.mk (t s) - (1 + X) * PowerSeries.mk (t s)
      + (X + X ^ 3 + X ^ 3) = 0 := by
  ext n
  rcases n with _ | _ | _ | _ | m
  · simp [t]
  · simp [coeff_mul, Finset.Nat.antidiagonal_succ, t, h1, add_mul, coeff_X, coeff_X_pow]
  · simp [coeff_mul, Finset.Nat.antidiagonal_succ, t, h1, h2, add_mul, coeff_X, coeff_X_pow]
  · simp [coeff_mul, Finset.Nat.antidiagonal_succ, t, h1, h2, h3, add_mul, coeff_X, coeff_X_pow]
  · have hc := conv s h1 h2 hrec m
    have j1 : ¬ (m + 4 = 1) := by omega
    have j3 : ¬ (m + 4 = 3) := by omega
    rw [map_add, map_sub, hc, add_mul, one_mul, map_add, coeff_succ_X_mul, coeff_mk, coeff_mk,
      map_add, map_add, coeff_X, coeff_X_pow, if_neg j1, if_neg j3, t_succ, t_succ, map_zero]
    ring

/-- The first order differential equation, with all terms written as monomials. -/
lemma ode (s : ℕ → ℤ) (h1 : s 1 = 1) (h2 : s 2 = 0) (h3 : s 3 = 2)
    (hrec : ∀ n : ℕ, 4 ≤ n → s n = ∑ k ∈ Finset.Icc 1 (n - 3), s k * s (n - k)) :
    C (-4 : ℤ) * (X ^ 0 * d⁄dX ℤ (PowerSeries.mk (t s)))
      + C (8 : ℤ) * (X ^ 1 * d⁄dX ℤ (PowerSeries.mk (t s)))
      + C (-4 : ℤ) * (X ^ 2 * d⁄dX ℤ (PowerSeries.mk (t s)))
      + C (32 : ℤ) * (X ^ 3 * d⁄dX ℤ (PowerSeries.mk (t s)))
      + C (-4 : ℤ) * (X ^ 0 * PowerSeries.mk (t s)) + C (4 : ℤ) * (X ^ 1 * PowerSeries.mk (t s))
      + C (-48 : ℤ) * (X ^ 2 * PowerSeries.mk (t s))
      = C (-4 : ℤ) * X ^ 0 + C (4 : ℤ) * X ^ 1 + C (-24 : ℤ) * X ^ 2 + C (-8 : ℤ) * X ^ 3 := by
  have hE := quad s h1 h2 h3 hrec
  have hD := congrArg (d⁄dX ℤ) hE
  simp only [map_sub, map_add, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, derivative_one, smul_eq_mul, nsmul_eq_mul] at hD
  simp only [eq_intCast]
  push_cast at hD ⊢
  linear_combination
    (4 * ((1 + X) - 2 * PowerSeries.mk (t s))) * hD
    + (16 * d⁄dX ℤ (PowerSeries.mk (t s)) - 8) * hE

/-- The recurrence read off from the differential equation at the coefficient of `x^(k+6)`. -/
lemma rec (s : ℕ → ℤ) (h1 : s 1 = 1) (h2 : s 2 = 0) (h3 : s 3 = 2)
    (hrec : ∀ n : ℕ, 4 ≤ n → s n = ∑ k ∈ Finset.Icc 1 (n - 3), s k * s (n - k)) (k : ℕ) :
    -4 * (s (k + 7) * ((k : ℤ) + 7)) + 8 * (s (k + 6) * ((k : ℤ) + 6))
      + -4 * (s (k + 5) * ((k : ℤ) + 5)) + 32 * (s (k + 4) * ((k : ℤ) + 4))
      + -4 * s (k + 6) + 4 * s (k + 5) + -48 * s (k + 4) = 0 := by
  have hc := congrArg (coeff (k + 6)) (ode s h1 h2 h3 hrec)
  simp only [map_add, coeff_C_mul, coeff_X_pow_mul', coeff_derivative, coeff_mk, coeff_X_pow]
    at hc
  have i0 : (0 : ℕ) ≤ k + 6 := by omega
  have i1 : (1 : ℕ) ≤ k + 6 := by omega
  have i2 : (2 : ℕ) ≤ k + 6 := by omega
  have i3 : (3 : ℕ) ≤ k + 6 := by omega
  have j0 : ¬ (k + 6 = 0) := by omega
  have j1 : ¬ (k + 6 = 1) := by omega
  have j2 : ¬ (k + 6 = 2) := by omega
  have j3 : ¬ (k + 6 = 3) := by omega
  have t1 : k + 6 - 1 = k + 5 := by omega
  have t2 : k + 6 - 2 = k + 4 := by omega
  have t3 : k + 6 - 3 = k + 3 := by omega
  have u0 : k + 6 + 1 = k + 7 := by omega
  have u1 : k + 5 + 1 = k + 6 := by omega
  have u2 : k + 4 + 1 = k + 5 := by omega
  have u3 : k + 3 + 1 = k + 4 := by omega
  have v7 : t s (k + 7) = s (k + 7) := t_succ s (k + 6)
  have v6 : t s (k + 6) = s (k + 6) := t_succ s (k + 5)
  have v5 : t s (k + 5) = s (k + 5) := t_succ s (k + 4)
  have v4 : t s (k + 4) = s (k + 4) := t_succ s (k + 3)
  simp only [i0, i1, i2, i3, j0, j1, j2, j3, t1, t2, t3, if_true, if_false,
    Nat.sub_zero, mul_zero, add_zero, u0, u1, u2, u3, v7, v6, v5, v4] at hc
  push_cast at hc ⊢
  linarith

end OMA.P025249

open OMA.S_oeis_a025249 OMA.P025249 in
theorem OMA.solution : type_of% @OMA.S_oeis_a025249.main := by
  intro s h1 h2 h3 hrec n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have hr := rec s h1 h2 h3 hrec k
  have hq := congrArg (Int.cast : ℤ → ℚ) hr
  have e1 : k + 4 - 1 + 3 = k + 6 := by omega
  have e2 : k + 4 - 2 + 3 = k + 5 := by omega
  have e3 : k + 4 - 3 + 3 = k + 4 := by omega
  have e0 : k + 4 + 3 = k + 7 := by omega
  unfold a
  rw [e1, e2, e3, e0]
  push_cast at hq ⊢
  linarith
