import OMAStatements.S_oeis_a257889
import Mathlib

namespace OMA.P_oeis_a257889

private theorem main_proved :
    ∀ (a b : ℕ → ℤ),
      a 0 = 1 →
      a 1 = 1 →
      (∀ n : ℕ, b n = PowerSeries.coeff n (PowerSeries.mk a ^ 2)) →
      (∀ n : ℕ, 1 ≤ n → a (2 * n) = a n * b n ∧ a (2 * n + 1) = a n * b (n + 1)) →
      ∀ n : ℕ, (5 : ℤ) ∣ a (3 * 2 ^ n) := by
  intro a b ha0 ha1 hb hrec
  have hb_sum : ∀ m : ℕ, b m = ∑ i ∈ Finset.range (m + 1), a i * a (m - i) := by
    intro m
    rw [hb m, pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (f := fun i j => PowerSeries.coeff i (PowerSeries.mk a) * PowerSeries.coeff j (PowerSeries.mk a))]
    simp [PowerSeries.coeff_mk]
  have hb1 : b 1 = 2 := by
    rw [hb_sum 1, Finset.sum_range_succ, Finset.sum_range_one]
    simp [ha0, ha1]
  have ha2 : a 2 = 2 := by
    have h := (hrec 1 (by omega)).1
    rw [ha1, hb1] at h
    simpa using h
  have hb2 : b 2 = 5 := by
    rw [hb_sum 2, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp [ha0, ha1, ha2]
  have ha3 : a 3 = 5 := by
    have h := (hrec 1 (by omega)).2
    rw [ha1, hb2] at h
    simpa using h
  intro n
  induction n with
  | zero =>
    simp [ha3]
  | succ k ih =>
    have hmul : 3 * 2 ^ (k + 1) = 2 * (3 * 2 ^ k) := by ring
    rw [hmul, (hrec (3 * 2 ^ k) (by have : 1 ≤ 2 ^ k := Nat.one_le_two_pow; omega)).1]
    exact dvd_mul_of_dvd_left ih _

end OMA.P_oeis_a257889

theorem OMA.solution : type_of% @OMA.S_oeis_a257889.main :=
  OMA.P_oeis_a257889.main_proved
