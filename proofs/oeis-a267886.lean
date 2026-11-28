import OMAStatements.S_oeis_a267886

/-! Rule 235 is uniformly on after stage 3. Each following row appends two on digits. -/
open OMA.S_oeis_a267886 PowerSeries Finset

private theorem uniform (t : ℕ) : ∀ i : ℤ, state (t + 3) i = true := by
  induction t with
  | zero =>
    intro i
    change state 3 i = true
    by_cases far : i < -3 ∨ 3 < i
    · have off (j : ℤ) (h : i-3 ≤ j) (h' : j ≤ i+3) : j ≠ 0 := by omega
      simp (disch := omega) [state, off, eca] <;> decide
    have lo : -3 ≤ i := by omega
    have hi : i ≤ 3 := by omega
    interval_cases i <;> decide
  | succ t ih =>
    intro i
    change eca 235 (state (t + 3) (i-1)) (state (t + 3) i)
      (state (t + 3) (i+1)) = true
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

private theorem next_row (n : ℕ) (hn : 3 ≤ n) :
    a (n+1) = 4 * a n + 3 := by
  have row (m : ℕ) (hm : 3 ≤ m) :
      a m = ∑ k ∈ range (2*m+1), 2 ^ (2*m-k) := by
    have on (x : ℤ) : state m x = true := by
      simpa only [Nat.sub_add_cancel hm] using uniform (m-3) x
    simp [a, on]
  rw [row n hn, row (n+1) (by omega), geomWindow]
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a267886.main := by
  have recurrence : ∀ n : ℕ, 4 < n →
      (a n : ℤ) = 5 * a (n-1) - 4 * a (n-2) := by
    intro n hn
    have h := next_row (n-1) (by omega)
    have g := next_row (n-2) (by omega)
    rw [show n-1+1=n by omega] at h
    rw [show n-2+1=n-1 by omega] at g
    omega
  refine ⟨recurrence, ?_⟩
  have h0 : a 0 = 1 := by decide +kernel
  have h1 : a 1 = 4 := by decide +kernel
  have h2 : a 2 = 27 := by decide +kernel
  have h3 : a 3 = 127 := by decide +kernel
  have h4 : a 4 = 511 := by decide +kernel
  have den (F : PowerSeries ℤ) :
      F * ((1 - X) * (1 - 4 * X)) =
        F - C (5 : ℤ) * (F * X^1) + C (4 : ℤ) * (F * X^2) := by
    norm_num <;> ring
  have num : (1 - X + 11 * X ^ 2 + 8 * X ^ 3 - 16 * X ^ 4 : PowerSeries ℤ) =
      C (1 : ℤ) + C (-1 : ℤ) * X^1 + C (11 : ℤ) * X^2 + C (8 : ℤ) * X^3 + C (-16 : ℤ) * X^4 := by norm_num <;> ring
  rw [den, num]
  apply PowerSeries.ext
  intro n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow,
    coeff_C, coeff_mk]
  by_cases hn : 4 < n
  · have h := recurrence n hn
    split_ifs <;> omega
  · interval_cases n <;> norm_num [h0, h1, h2, h3, h4]
