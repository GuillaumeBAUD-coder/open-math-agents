import OMAStatements.S_oeis_a223173
import Mathlib

namespace A223173Proof
open OMA.S_oeis_a223173

lemma s0 : Nat.stirlingFirst 3 0 = 0 := by decide
lemma s1 : Nat.stirlingFirst 3 1 = 2 := by decide
lemma s2 : Nat.stirlingFirst 3 2 = 3 := by decide
lemma s3 : Nat.stirlingFirst 3 3 = 1 := by decide

lemma a_eq (n : ℕ) : a n = 2 * 2 ^ n - 3 * 3 ^ n + 4 ^ n := by
  simp only [a, stirling1, Finset.sum_range_succ, Finset.sum_range_zero, s0, s1, s2, s3]
  norm_num
  ring

lemma b_eq (n : ℕ) : (if n = 0 then (0 : ℤ) else a n) = 2 * 2 ^ n - 3 * 3 ^ n + 4 ^ n := by
  split_ifs with h
  · subst h
    norm_num
  · exact a_eq n

end A223173Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a223173.main := by
  refine ⟨?_, ?_⟩
  · intro n _
    rw [A223173Proof.a_eq]
    ring
  · have hb : (fun n : ℕ => if n = 0 then (0 : ℤ) else OMA.S_oeis_a223173.a n)
        = fun n : ℕ => 2 * 2 ^ n - 3 * 3 ^ n + 4 ^ n := funext A223173Proof.b_eq
    rw [hb]
    have e : ∀ A : PowerSeries ℤ,
        A * ((2 * PowerSeries.X - 1) * (3 * PowerSeries.X - 1) * (4 * PowerSeries.X - 1))
          = (24 : ℕ) • (A * PowerSeries.X ^ 3) - (26 : ℕ) • (A * PowerSeries.X ^ 2)
            + (9 : ℕ) • (A * PowerSeries.X ^ 1) - A := by
      intro A
      simp only [nsmul_eq_mul]
      push_cast
      ring
    have r : (-PowerSeries.X * (6 * PowerSeries.X - 1) : PowerSeries ℤ)
        = PowerSeries.X ^ 1 - (6 : ℕ) • PowerSeries.X ^ 2 := by
      simp only [nsmul_eq_mul]
      push_cast
      ring
    rw [e, r]
    ext n
    rw [map_sub, map_add, map_sub, map_nsmul, map_nsmul, map_nsmul, map_sub, map_nsmul,
      PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow]
    rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | rfl | h
    · norm_num
    · norm_num [PowerSeries.coeff_mk]
    · norm_num [PowerSeries.coeff_mk]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      have e1 : m + 3 - 3 = m := by omega
      have e2 : m + 3 - 2 = m + 1 := by omega
      have e3 : m + 3 - 1 = m + 2 := by omega
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega),
        if_neg (by omega), PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
        e1, e2, e3]
      simp only [nsmul_eq_mul, mul_zero, sub_zero]
      push_cast
      ring
