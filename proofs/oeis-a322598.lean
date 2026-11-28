import OMAStatements.S_oeis_a322598
import Mathlib

namespace OMA.S_oeis_a322598
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

lemma emodP (x : ℤ) : ((9 * x ^ 2 + 4 * x + 3) % 12 = 3 ∧ x % 6 = 0) ∨
    ((9 * x ^ 2 + 4 * x + 3) % 12 = 4 ∧ x % 6 = 1) ∨ ((9 * x ^ 2 + 4 * x + 3) % 12 = 11 ∧ x % 6 = 2) ∨
    ((9 * x ^ 2 + 4 * x + 3) % 12 = 0 ∧ x % 6 = 3) ∨ ((9 * x ^ 2 + 4 * x + 3) % 12 = 7 ∧ x % 6 = 4) ∨
    ((9 * x ^ 2 + 4 * x + 3) % 12 = 8 ∧ x % 6 = 5) := by
  have h : 9 * x ^ 2 + 4 * x + 3 = (9 * (x % 6) ^ 2 + 4 * (x % 6) + 3) +
      12 * (27 * (x / 6) ^ 2 + 9 * (x / 6) * (x % 6) + 2 * (x / 6)) := by
    generalize hq : x / 6 = q
    generalize hr : x % 6 = r
    have hx : x = r + 6 * q := by omega
    subst hx
    ring
  have hr0 : 0 ≤ x % 6 := Int.emod_nonneg _ (by norm_num)
  have hr1 : x % 6 < 6 := Int.emod_lt_of_pos _ (by norm_num)
  rw [h, Int.add_mul_emod_self_left]
  generalize x % 6 = r at *
  interval_cases r <;> simp

lemma link (k : ℕ) : ∃ P R : ℤ, P = 9 * (k : ℤ) ^ 2 + 4 * k + 3 ∧ 12 * a k + R = P ∧
    ((R = 3 ∧ (k : ℤ) % 6 = 0) ∨ (R = 4 ∧ (k : ℤ) % 6 = 1) ∨ (R = 11 ∧ (k : ℤ) % 6 = 2) ∨
     (R = 0 ∧ (k : ℤ) % 6 = 3) ∨ (R = 7 ∧ (k : ℤ) % 6 = 4) ∨ (R = 8 ∧ (k : ℤ) % 6 = 5)) := by
  refine ⟨9 * (k : ℤ) ^ 2 + 4 * k + 3, (9 * (k : ℤ) ^ 2 + 4 * k + 3) % 12, rfl, ?_, ?_⟩
  · simp only [a]
    generalize 9 * (k : ℤ) ^ 2 + 4 * k + 3 = P
    omega
  · exact emodP (k : ℤ)

lemma recur (m : ℕ) : a (m + 6) = a (m + 5) + a (m + 4) - a (m + 2) - a (m + 1) + a m := by
  obtain ⟨P6, R6, hP6, h6, c6⟩ := link (m + 6)
  obtain ⟨P5, R5, hP5, h5, c5⟩ := link (m + 5)
  obtain ⟨P4, R4, hP4, h4, c4⟩ := link (m + 4)
  obtain ⟨P2, R2, hP2, h2, c2⟩ := link (m + 2)
  obtain ⟨P1, R1, hP1, h1, c1⟩ := link (m + 1)
  obtain ⟨P0, R0, hP0, h0, c0⟩ := link m
  have poly : P6 - P5 - P4 + P2 + P1 - P0 = 0 := by
    rw [hP6, hP5, hP4, hP2, hP1, hP0]; push_cast; ring
  push_cast at c6 c5 c4 c2 c1
  clear hP6 hP5 hP4 hP2 hP1 hP0
  omega

end OMA.S_oeis_a322598

theorem OMA.solution : type_of% @OMA.S_oeis_a322598.main := by
  open OMA.S_oeis_a322598 in
  refine ⟨?_, ?_⟩
  · ext n
    rw [gf_poly _ _ (fun k => [1, -1, -1, 0, 1, 1, -1].getD k 0) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; simp; (try simp only [map_ofNat]); ring),
      coeff_poly _ (fun k => [0, 1, 2, 4, 2].getD k (0:ℚ)) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; simp; (try simp only [map_ofNat]); ring)]
    rcases Nat.lt_or_ge n 6 with h | h
    · interval_cases n <;> simp [Finset.sum_range_succ, a] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      have := recur m
      have h2 : (a (m + 6) : ℚ) = a (m + 5) + a (m + 4) - a (m + 2) - a (m + 1) + a m := by
        exact_mod_cast this
      simp [Finset.sum_range_succ, (by omega : m + 6 - 1 = m + 5), (by omega : m + 6 - 2 = m + 4),
        (by omega : m + 6 - 3 = m + 3), (by omega : m + 6 - 4 = m + 2), (by omega : m + 6 - 5 = m + 1),
        (by omega : m + 6 - 6 = m)]
      linarith
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    have := recur (m + 1)
    simp only [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
      show m + 7 - 4 = m + 3 by omega, show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega]
    exact this
