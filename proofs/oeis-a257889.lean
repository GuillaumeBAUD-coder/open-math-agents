import OMAStatements.S_oeis_a257889
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a257889.main := by
  intro a b h0 h1 hb hrec n
  have hb1 : b 1 = 2 := by
    rw [hb 1, pow_two, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [Finset.sum_range_succ, PowerSeries.coeff_mk, h0, h1]
  have ha2 : a 2 = 2 := by
    have h := (hrec 1 le_rfl).1
    simpa [h1, hb1] using h
  have hb2 : b 2 = 5 := by
    rw [hb 2, pow_two, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [Finset.sum_range_succ, PowerSeries.coeff_mk, h0, h1, ha2]
  have ha3 : a 3 = 5 := by
    have h := (hrec 1 le_rfl).2
    simpa [h1, hb2] using h
  induction n with
  | zero => simp [ha3]
  | succ k ih =>
    have h := (hrec (3 * 2 ^ k) (Nat.mul_pos (by norm_num) (pow_pos (by norm_num) k))).1
    have e : 3 * 2 ^ (k + 1) = 2 * (3 * 2 ^ k) := by ring
    rw [e, h]
    exact Dvd.dvd.mul_right ih _
