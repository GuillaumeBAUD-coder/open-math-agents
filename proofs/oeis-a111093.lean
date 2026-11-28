import OMAStatements.S_oeis_a111093

/-! Credit: @unserus

position (n+20) - position n = 10 (2n^2 + 42n + 287), so the added digit has period 20;
the recurrence reduces to d(m+15) - d(m+10) + d(m+5) - d(m) = 0, checked on one period, and the
generating function follows coefficientwise (first 16 terms computed). -/

namespace OMAA111093Helpers
open OMA.S_oeis_a111093 PowerSeries

theorem pos20 (n : ℕ) : position (n + 20) = position n + 10 * (2 * n ^ 2 + 42 * n + 287) := by
  simp only [position]
  ring

def d (n : ℕ) : ℤ := ((position n % 10 : ℕ) : ℤ)

theorem d20 (n : ℕ) : d (n + 20) = d n := by
  simp only [d, pos20]
  congr 1
  omega

theorem dper (q r : ℕ) : d (20 * q + r) = d r := by
  induction q with
  | zero => simp
  | succ q ih => rw [show 20 * (q + 1) + r = (20 * q + r) + 20 by ring, d20, ih]

theorem a_succ (n : ℕ) : a (n + 1) = a n + d (n + 1) := rfl

theorem key (m : ℕ) : d (m + 15) - d (m + 10) + d (m + 5) - d m = 0 := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 20 ∧ m = 20 * q + r := ⟨m / 20, m % 20, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 20).symm⟩
  rw [show 20 * q + r + 15 = 20 * q + (r + 15) by ring, show 20 * q + r + 10 = 20 * q + (r + 10) by ring,
    show 20 * q + r + 5 = 20 * q + (r + 5) by ring, dper, dper, dper, dper]
  interval_cases r <;> decide

theorem rec (m : ℕ) : a (m + 16) = a (m + 15) + a (m + 11) - a (m + 10) - a (m + 6) + a (m + 5)
    + a (m + 1) - a m := by
  have h16 := a_succ (m + 15)
  have h11 := a_succ (m + 10)
  have h6 := a_succ (m + 5)
  have h1 := a_succ m
  have hk := key (m + 1)
  rw [show m + 15 + 1 = m + 16 by ring] at h16
  rw [show m + 10 + 1 = m + 11 by ring] at h11
  rw [show m + 5 + 1 = m + 6 by ring] at h6
  rw [show m + 1 + 15 = m + 16 by ring, show m + 1 + 10 = m + 11 by ring,
    show m + 1 + 5 = m + 6 by ring] at hk
  generalize a (m + 16) = x16 at *
  generalize a (m + 15) = x15 at *
  generalize a (m + 11) = x11 at *
  generalize a (m + 10) = x10 at *
  generalize a (m + 6) = x6 at *
  generalize a (m + 5) = x5 at *
  generalize a (m + 1) = x1 at *
  generalize a m = x0 at *
  generalize d (m + 16) = e16 at *
  generalize d (m + 11) = e11 at *
  generalize d (m + 6) = e6 at *
  generalize d (m + 1) = e1 at *
  linear_combination h16 - h11 + h6 - h1 + hk

theorem small : a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 6 ∧ a 3 = 10 ∧ a 4 = 10 ∧ a 5 = 15 ∧ a 6 = 16 ∧
    a 7 = 16 ∧ a 8 = 20 ∧ a 9 = 25 ∧ a 10 = 30 ∧ a 11 = 36 ∧ a 12 = 36 ∧ a 13 = 45 ∧
    a 14 = 50 ∧ a 15 = 50 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end OMAA111093Helpers

open OMAA111093Helpers OMA.S_oeis_a111093 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a111093.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 16 := ⟨n - 16, by omega⟩
    rw [show m + 16 - 1 = m + 15 by omega, show m + 16 - 5 = m + 11 by omega,
      show m + 16 - 6 = m + 10 by omega, show m + 16 - 10 = m + 6 by omega,
      show m + 16 - 11 = m + 5 by omega, show m + 16 - 15 = m + 1 by omega,
      show m + 16 - 16 = m by omega]
    exact rec m
  · dsimp only
    have hL : ((X ^ 16 - X ^ 15 - X ^ 11 + X ^ 10 + X ^ 6 - X ^ 5 - X + 1) * mk a : ℤ⟦X⟧) =
        X ^ 16 * mk a - X ^ 15 * mk a - X ^ 11 * mk a + X ^ 10 * mk a + X ^ 6 * mk a
          - X ^ 5 * mk a - X ^ 1 * mk a + mk a := by ring
    have hR : (X * (9 * X ^ 12 + 5 * X ^ 11 + 6 * X ^ 10 + 5 * X ^ 8 - 5 * X ^ 6 + 5 * X ^ 4
        + 4 * X ^ 2 + 5 * X + 1) : ℤ⟦X⟧) =
        C (9 : ℤ) * X ^ 13 + C (5 : ℤ) * X ^ 12 + C (6 : ℤ) * X ^ 11 + C (5 : ℤ) * X ^ 9
          - C (5 : ℤ) * X ^ 7 + C (5 : ℤ) * X ^ 5 + C (4 : ℤ) * X ^ 3 + C (5 : ℤ) * X ^ 2 + X ^ 1 := by
      simp only [map_ofNat]; ring
    rw [hL, hR]
    ext k
    simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
    rcases Nat.lt_or_ge k 16 with hk | hk
    · obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15⟩ := small
      interval_cases k <;> simp [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15]
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 16 := ⟨k - 16, by omega⟩
      rw [if_pos (by omega : 16 ≤ m + 16), if_pos (by omega : 15 ≤ m + 16),
        if_pos (by omega : 11 ≤ m + 16), if_pos (by omega : 10 ≤ m + 16),
        if_pos (by omega : 6 ≤ m + 16), if_pos (by omega : 5 ≤ m + 16),
        if_pos (by omega : 1 ≤ m + 16),
        if_neg (by omega : ¬ m + 16 = 13), if_neg (by omega : ¬ m + 16 = 12),
        if_neg (by omega : ¬ m + 16 = 11), if_neg (by omega : ¬ m + 16 = 9),
        if_neg (by omega : ¬ m + 16 = 7), if_neg (by omega : ¬ m + 16 = 5),
        if_neg (by omega : ¬ m + 16 = 3), if_neg (by omega : ¬ m + 16 = 2),
        if_neg (by omega : ¬ m + 16 = 1),
        show m + 16 - 16 = m by omega, show m + 16 - 15 = m + 1 by omega,
        show m + 16 - 11 = m + 5 by omega, show m + 16 - 10 = m + 6 by omega,
        show m + 16 - 6 = m + 10 by omega, show m + 16 - 5 = m + 11 by omega,
        show m + 16 - 1 = m + 15 by omega]
      have h := rec m
      generalize a (m + 16) = x16 at *
      generalize a (m + 15) = x15 at *
      generalize a (m + 11) = x11 at *
      generalize a (m + 10) = x10 at *
      generalize a (m + 6) = x6 at *
      generalize a (m + 5) = x5 at *
      generalize a (m + 1) = x1 at *
      generalize a m = x0 at *
      linear_combination h
