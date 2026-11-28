import OMAStatements.S_oeis_a192069

/-!
Proof of the conjectured generating function of A192069.
Credit: @rtflynn (agent: Claude Code, model claude-opus-5-5)

1. `X^k` is congruent to `F_k X + (F_{k+1} - F_k)` modulo `X^2 - X - 1`, so the reduction of
   `p m` is `S m * X + T m` with `S m = ∑_{k ≤ m} C(k+4,4) F_k`, and A192249(n) = S (n-1).
2. By induction, `S m = G (m+1)` with the closed form
   `24 G n = (72 - 44n - 4n^3) F_n + (120 - 50n + 23n^2 + 2n^3 + n^4) F_{n+1} - 120`.
3. The coefficient of `x^n` in the product is a combination of `G (n-j)`, `j ≤ 11`. For `n < 11`
   it is computed; for `n ≥ 11` all Fibonacci numbers are written through `F_m`, `F_{m+1}`
   (`n = m + 11`) and the combination vanishes identically.
-/

namespace OMA.P_oeis_a192069

open Polynomial OMA.S_oeis_a192069

lemma q_monic : (X ^ 2 - X - 1 : ℤ[X]).Monic := by
  monicity!

lemma q_degree : (X ^ 2 - X - 1 : ℤ[X]).degree = 2 := by
  compute_degree!

lemma dvd_pow (k : ℕ) :
    (X ^ 2 - X - 1 : ℤ[X]) ∣
      X ^ k - (C ((Nat.fib k : ℕ) : ℤ) * X + C ((Nat.fib (k + 1) : ℤ) - Nat.fib k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨X * t + C ((Nat.fib k : ℕ) : ℤ), ?_⟩
    have h2 : ((Nat.fib (k + 1 + 1) : ℕ) : ℤ) = Nat.fib k + Nat.fib (k + 1) := by
      rw [Nat.fib_add_two]; push_cast; ring
    rw [h2]
    simp only [map_sub, map_add] at ht ⊢
    linear_combination X * ht

/-- `S m = ∑_{k ≤ m} C(k+4,4) F_k`: the coefficient of `x` in the reduction of `p m`. -/
def S (m : ℕ) : ℤ := ∑ k ∈ Finset.range (m + 1), ((k + 4).choose 4 : ℤ) * Nat.fib k

/-- The constant term of the reduction of `p m`. -/
def T (m : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (m + 1), ((k + 4).choose 4 : ℤ) * ((Nat.fib (k + 1) : ℤ) - Nat.fib k)

lemma dvd_p (m : ℕ) : (X ^ 2 - X - 1 : ℤ[X]) ∣ p m - (C (S m) * X + C (T m)) := by
  induction m with
  | zero => simp [p, S, T]
  | succ m ih =>
    have key : p (m + 1) - (C (S (m + 1)) * X + C (T (m + 1))) =
        (p m - (C (S m) * X + C (T m))) + C (((m + 1 + 4).choose 4 : ℕ) : ℤ) *
          (X ^ (m + 1) - (C ((Nat.fib (m + 1) : ℕ) : ℤ) * X +
            C ((Nat.fib (m + 1 + 1) : ℤ) - Nat.fib (m + 1)))) := by
      rw [p, p, S, S, T, T, Finset.sum_range_succ _ (m + 1), Finset.sum_range_succ _ (m + 1),
        Finset.sum_range_succ _ (m + 1)]
      simp only [map_add, map_mul, map_sub]
      ring
    rw [key]
    exact dvd_add ih (dvd_mul_of_dvd_right (dvd_pow (m + 1)) _)

lemma reduce_p (m : ℕ) : reduce (p m) = C (S m) * X + C (T m) := by
  unfold reduce
  rw [modByMonic_eq_of_dvd_sub q_monic (dvd_p m), (modByMonic_eq_self_iff q_monic).2]
  rw [q_degree]
  exact lt_of_le_of_lt degree_linear_le (by decide)

lemma A192249_eq (n : ℕ) : A192249 n = S (n - 1) := by
  rw [A192249, reduce_p, coeff_add, coeff_C_mul_X, coeff_C]
  simp only [if_true, one_ne_zero, if_false, add_zero]

lemma choose4 (k : ℕ) :
    ((k + 4).choose 4 : ℚ) = (k + 4) * (k + 3) * (k + 2) * (k + 1) / 24 := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (k + 4) 4
  have hd : (k + 4).descFactorial 4 = (k + 4) * (k + 3) * (k + 2) * (k + 1) := by
    simp [Nat.descFactorial_succ]
    ring
  rw [hd, show Nat.factorial 4 = 24 by decide] at h
  have h' : ((k + 4 : ℕ) : ℚ) * ((k + 3 : ℕ) : ℚ) * ((k + 2 : ℕ) : ℚ) * ((k + 1 : ℕ) : ℚ) =
      24 * ((k + 4).choose 4 : ℚ) := by exact_mod_cast h
  push_cast at h'
  rw [h']
  ring

/-- The closed form of the partial sums. -/
noncomputable def G (n : ℕ) : ℚ :=
  ((72 - 44 * (n : ℚ) - 4 * (n : ℚ) ^ 3) * Nat.fib n +
    (120 - 50 * (n : ℚ) + 23 * (n : ℚ) ^ 2 + 2 * (n : ℚ) ^ 3 + (n : ℚ) ^ 4) * Nat.fib (n + 1) -
      120) / 24

lemma S_eq (m : ℕ) : (S m : ℚ) = G (m + 1) := by
  induction m with
  | zero => norm_num [S, G]
  | succ m ih =>
    have hS : (S (m + 1) : ℚ) = S m + ((m + 1 + 4).choose 4 : ℚ) * Nat.fib (m + 1) := by
      rw [S, S, Finset.sum_range_succ _ (m + 1)]
      push_cast
      ring
    rw [hS, ih, choose4]
    have hf : (Nat.fib (m + 1 + 1 + 1) : ℚ) = Nat.fib (m + 1) + Nat.fib (m + 1 + 1) := by
      rw [Nat.fib_add_two]; push_cast; ring
    simp only [G]
    rw [hf]
    push_cast
    ring

lemma f_eq (n : ℕ) : (if n = 0 then (0 : ℚ) else a n) = G n / 5 := by
  rcases n with _ | k
  · norm_num [G]
  · simp only [Nat.add_one_ne_zero, if_false, a, A192249_eq, Nat.add_sub_cancel]
    rw [S_eq]

end OMA.P_oeis_a192069

open OMA.P_oeis_a192069 in
theorem OMA.solution : type_of% @OMA.S_oeis_a192069.main := by
  have hA : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else OMA.S_oeis_a192069.a n) =
      PowerSeries.mk (fun n => G n / 5) := by
    congr 1
    funext n
    exact f_eq n
  rw [hA]
  set A := PowerSeries.mk (fun n => G n / 5) with hAdef
  have hD : A * ((PowerSeries.X - 1) * (PowerSeries.X ^ 2 + PowerSeries.X - 1) ^ 5) =
      (A + 10 • (A * PowerSeries.X ^ 2) + 5 • (A * PowerSeries.X ^ 3) +
          4 • (A * PowerSeries.X ^ 5) + 26 • (A * PowerSeries.X ^ 6) +
          4 • (A * PowerSeries.X ^ 10) + A * PowerSeries.X ^ 11) -
        (6 • (A * PowerSeries.X ^ 1) + 25 • (A * PowerSeries.X ^ 4) +
          5 • (A * PowerSeries.X ^ 7) + 15 • (A * PowerSeries.X ^ 8)) := by
    ring
  have hN : (PowerSeries.X : PowerSeries ℚ) ^ 2 *
      (1 - 2 * PowerSeries.X + 4 * PowerSeries.X ^ 2 - 3 * PowerSeries.X ^ 3 +
        PowerSeries.X ^ 4) =
      (PowerSeries.X ^ 2 + 4 • PowerSeries.X ^ 4 + PowerSeries.X ^ 6) -
        (2 • PowerSeries.X ^ 3 + 3 • PowerSeries.X ^ 5) := by
    ring
  rw [hD, hN]
  ext n
  simp only [map_add, map_sub, map_nsmul]
  simp only [PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, hAdef, PowerSeries.coeff_mk,
    nsmul_eq_mul]
  rcases lt_or_ge n 11 with hn | hn
  · interval_cases n <;> norm_num [G]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
    have e : ∀ j, j ≤ 11 → j ≤ m + 11 := fun j hj => by omega
    simp only [e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num), e 4 (by norm_num),
      e 5 (by norm_num), e 6 (by norm_num), e 7 (by norm_num), e 8 (by norm_num),
      e 10 (by norm_num), e 11 (by norm_num), if_true,
      show m + 11 ≠ 2 by omega, show m + 11 ≠ 3 by omega, show m + 11 ≠ 4 by omega,
      show m + 11 ≠ 5 by omega, show m + 11 ≠ 6 by omega, if_false,
      show m + 11 - 1 = m + 10 by omega, show m + 11 - 2 = m + 9 by omega,
      show m + 11 - 3 = m + 8 by omega, show m + 11 - 4 = m + 7 by omega,
      show m + 11 - 5 = m + 6 by omega, show m + 11 - 6 = m + 5 by omega,
      show m + 11 - 7 = m + 4 by omega, show m + 11 - 8 = m + 3 by omega,
      show m + 11 - 10 = m + 1 by omega, show m + 11 - 11 = m by omega]
    have f2 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
    have f3 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
    have f4 : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := Nat.fib_add_two
    have f5 : Nat.fib (m + 5) = Nat.fib (m + 3) + Nat.fib (m + 4) := Nat.fib_add_two
    have f6 : Nat.fib (m + 6) = Nat.fib (m + 4) + Nat.fib (m + 5) := Nat.fib_add_two
    have f7 : Nat.fib (m + 7) = Nat.fib (m + 5) + Nat.fib (m + 6) := Nat.fib_add_two
    have f8 : Nat.fib (m + 8) = Nat.fib (m + 6) + Nat.fib (m + 7) := Nat.fib_add_two
    have f9 : Nat.fib (m + 9) = Nat.fib (m + 7) + Nat.fib (m + 8) := Nat.fib_add_two
    have f10 : Nat.fib (m + 10) = Nat.fib (m + 8) + Nat.fib (m + 9) := Nat.fib_add_two
    have f11 : Nat.fib (m + 11) = Nat.fib (m + 9) + Nat.fib (m + 10) := Nat.fib_add_two
    have f12 : Nat.fib (m + 12) = Nat.fib (m + 10) + Nat.fib (m + 11) := Nat.fib_add_two
    simp only [G, show m + 1 + 1 = m + 2 from rfl, show m + 3 + 1 = m + 4 from rfl,
      show m + 4 + 1 = m + 5 from rfl, show m + 5 + 1 = m + 6 from rfl,
      show m + 6 + 1 = m + 7 from rfl, show m + 7 + 1 = m + 8 from rfl,
      show m + 8 + 1 = m + 9 from rfl, show m + 9 + 1 = m + 10 from rfl,
      show m + 10 + 1 = m + 11 from rfl, show m + 11 + 1 = m + 12 from rfl]
    rw [f12, f11, f10, f9, f8, f7, f6, f5, f4, f3, f2]
    push_cast
    ring
