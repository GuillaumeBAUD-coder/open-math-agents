import OMAStatements.S_oeis_a147796
import Mathlib

namespace OMA.S_oeis_a147796
lemma gf_poly (f : ℕ → ℚ) (P : PowerSeries ℚ) (c : ℕ → ℚ) (m : ℕ)
    (hP : P = ∑ k ∈ Finset.range m, PowerSeries.C (c k) * PowerSeries.X ^ k) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * P) =
      ∑ k ∈ Finset.range m, c k * (if k ≤ n then f (n - k) else 0) := by
  rw [hP, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow']
  simp [PowerSeries.coeff_mk]

lemma coeff_poly (P : PowerSeries ℚ) (c : ℕ → ℚ) (m : ℕ)
    (hP : P = ∑ k ∈ Finset.range m, PowerSeries.C (c k) * PowerSeries.X ^ k) (n : ℕ) :
    PowerSeries.coeff n P = if n < m then c n else 0 := by
  rw [hP, map_sum]
  simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma ch3 (n : ℕ) : (6 * n.choose 3 : ℤ) = n * (n - 1) * (n - 2) := by
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> decide
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have := Nat.descFactorial_eq_factorial_mul_choose (m+3) 3
    simp [Nat.descFactorial_succ, Nat.factorial] at this
    have h2 : ((m + 3 - 2) * ((m + 3 - 1) * (m + 3)) : ℕ) = (m+1)*((m+2)*(m+3)) := by
      have : m + 3 - 2 = m + 1 := by omega
      have : m + 3 - 1 = m + 2 := by omega
      simp_all
    push_cast
    have h3 : (6 * (m+3).choose 3 : ℕ) = (m+1)*((m+2)*(m+3)) := by omega
    have h4 : ((6 * (m+3).choose 3 : ℕ) : ℤ) = (((m+1)*((m+2)*(m+3)) : ℕ) : ℤ) := by rw [h3]
    push_cast at h4
    linarith

lemma aq (n : ℕ) : (a n : ℚ) = (n * (n - 1) * (n - 2) / 6) * ((n:ℚ) ^ 3 - 5 * n - 6) := by
  have h := ch3 n
  have h' : (6 * (n.choose 3 : ℚ)) = n * (n - 1) * (n - 2) := by exact_mod_cast h
  simp only [a]
  push_cast
  rw [← h']; ring

lemma rec7 (m : ℕ) : (a (m+7) : ℚ) - 7 * a (m+6) + 21 * a (m+5) - 35 * a (m+4) + 35 * a (m+3)
    - 21 * a (m+2) + 7 * a (m+1) - a m = 0 := by
  simp only [aq]; push_cast; ring

end OMA.S_oeis_a147796

theorem OMA.solution : type_of% @OMA.S_oeis_a147796.main := by
  open OMA.S_oeis_a147796 in
  refine ⟨?_, ?_⟩
  · ext n
    rw [gf_poly _ _ (fun k => [1, -7, 21, -35, 35, -21, 7, -1].getD k 0) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; simp; simp only [map_ofNat]; ring),
      coeff_poly _ (fun k => [0, 0, 0, 6, 110, 2, 2].getD k (0:ℚ)) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; simp; simp only [map_ofNat]; ring)]
    rcases Nat.lt_or_ge n 7 with h | h
    · interval_cases n <;> simp [Finset.sum_range_succ, a, Nat.choose] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
      have := rec7 m
      simp [Finset.sum_range_succ, (by omega : m + 7 - 1 = m + 6), (by omega : m + 7 - 2 = m + 5),
        (by omega : m + 7 - 3 = m + 4), (by omega : m + 7 - 4 = m + 3), (by omega : m + 7 - 5 = m + 2),
        (by omega : m + 7 - 6 = m + 1), (by omega : m + 7 - 7 = m)]
      linarith
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    have h := rec7 m
    simp only [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
      show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega,
      show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega, show m + 7 - 7 = m by omega]
    have h2 : ((a (m+7) : ℤ) : ℚ) = ((7 * a (m+6) - 21 * a (m+5) + 35 * a (m+4) - 35 * a (m+3)
      + 21 * a (m+2) - 7 * a (m+1) + a m : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast h2
