import OMAStatements.S_oeis_a257889

-- Credit: @Dariusthedoggie
-- Proof: a(3) = 5 directly from the defining recurrence, and divisibility by 5 propagates to a(3*2^n) by induction

namespace OMA.P257889

theorem main_proof :
    ∀ (a b : ℕ → ℤ),
      a 0 = 1 →
      a 1 = 1 →
      (∀ n : ℕ, b n = PowerSeries.coeff n (PowerSeries.mk a ^ 2)) →
      (∀ n : ℕ, 1 ≤ n → a (2 * n) = a n * b n ∧ a (2 * n + 1) = a n * b (n + 1)) →
      ∀ n : ℕ, (5 : ℤ) ∣ a (3 * 2 ^ n) := by
  intro a b ha0 ha1 hb hrec
  have hb1 : b 1 = 2 := by
    rw [hb 1, sq, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [Finset.sum_range_succ, ha0, ha1]
  have ha2 : a 2 = 2 := by
    have h := (hrec 1 (by omega)).1
    simpa [ha1, hb1] using h
  have hb2 : b 2 = 5 := by
    rw [hb 2, sq, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [Finset.sum_range_succ, ha0, ha1, ha2]
  have ha3 : a 3 = 5 := by
    have h := (hrec 1 (by omega)).2
    simpa [ha1, hb2] using h
  intro n
  induction n with
  | zero =>
    simpa [ha3] using (dvd_refl (5 : ℤ))
  | succ k ih =>
    have hpos : 1 ≤ 3 * 2 ^ k := by
      have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
      omega
    have hstep : 3 * 2 ^ (k + 1) = 2 * (3 * 2 ^ k) := by ring
    rw [hstep, (hrec (3 * 2 ^ k) hpos).1]
    exact dvd_mul_of_dvd_left ih _

end OMA.P257889

theorem OMA.solution : type_of% @OMA.S_oeis_a257889.main := OMA.P257889.main_proof
