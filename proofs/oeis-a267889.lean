import OMAStatements.S_oeis_a267889

/-! Rule 239 is uniformly on after stage 2. Each following row appends two on digits. -/
open OMA.S_oeis_a267889 PowerSeries Finset

private theorem uniform (t : ℕ) : ∀ i : ℤ, state (t + 2) i = true := by
  induction t with
  | zero =>
    intro i
    change state 2 i = true
    by_cases far : i < -2 ∨ 2 < i
    · have off (j : ℤ) (h : i-2 ≤ j) (h' : j ≤ i+2) : j ≠ 0 := by omega
      simp (disch := omega) [state, off, eca] <;> decide
    have lo : -2 ≤ i := by omega
    have hi : i ≤ 2 := by omega
    interval_cases i <;> decide
  | succ t ih =>
    intro i
    change eca 239 (state (t + 2) (i-1)) (state (t + 2) i)
      (state (t + 2) (i+1)) = true
    simp only [ih]
    decide

private theorem geomWindow (b n : ℕ) :
    (∑ k ∈ Finset.range (2*(n+1)+1), b ^ (2*(n+1)-k)) =
    b^2 * (∑ k ∈ Finset.range (2*n+1), b ^ (2*n-k)) + b + 1 := by
  rw [show 2*(n+1)+1 = (2*n+1)+1+1 by omega]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.mul_sum]
  simp only [show 2*(n+1)-(2*n+1+1) = 0 by omega,
    show 2*(n+1)-(2*n+1) = 1 by omega, pow_zero, pow_one]
  congr 2
  apply Finset.sum_congr rfl
  intro k hk
  have h := Finset.mem_range.mp hk
  rw [← pow_add]
  congr 1
  omega

private theorem next_row (n : ℕ) (hn : 2 ≤ n) :
    a (n+1) = 100 * a n + 11 := by
  have row (m : ℕ) (hm : 2 ≤ m) :
      a m = ∑ k ∈ range (2*m+1), 10 ^ (2*m-k) := by
    have on (x : ℤ) : state m x = true := by
      simpa only [Nat.sub_add_cancel hm] using uniform (m-2) x
    simp [a, on]
  rw [row n hn, row (n+1) (by omega), geomWindow]
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a267889.main := by
  have recurrence : ∀ n : ℕ, 3 < n →
      (a n : ℤ) = 101 * a (n-1) - 100 * a (n-2) := by
    intro n hn
    have h := next_row (n-1) (by omega)
    have g := next_row (n-2) (by omega)
    rw [show n-1+1=n by omega] at h
    rw [show n-2+1=n-1 by omega] at g
    omega
  refine ⟨recurrence, ?_⟩
  have h0 : a 0 = 1 := by decide +kernel
  have h1 : a 1 = 110 := by decide +kernel
  have h2 : a 2 = 11111 := by decide +kernel
  have h3 : a 3 = 1111111 := by decide +kernel
  have den (F : PowerSeries ℤ) :
      F * ((1 - X) * (1 - 100 * X)) =
        F - C (101 : ℤ) * (F * X^1) + C (100 : ℤ) * (F * X^2) := by
    norm_num <;> ring
  have num : (1 + 9 * X + 101 * X ^ 2 - 100 * X ^ 3 : PowerSeries ℤ) =
      C (1 : ℤ) + C (9 : ℤ) * X^1 + C (101 : ℤ) * X^2 + C (-100 : ℤ) * X^3 := by norm_num <;> ring
  rw [den, num]
  apply PowerSeries.ext
  intro n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow,
    coeff_C, coeff_mk]
  by_cases hn : 3 < n
  · have h := recurrence n hn
    split_ifs <;> omega
  · interval_cases n <;> norm_num [h0, h1, h2, h3]
