import OMAStatements.S_oeis_a134119

-- Problem: A134119: a(n) = floor(n^2/10) - floor((n-1)^2/10).
-- Upstream: formal-conjectures statements/oeis-a134119.lean:0 (declaration OMA.S_oeis_a134119.main)
-- Credit: @Kutomiy (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open PowerSeries OMA.S_oeis_a134119

lemma OMA.a_int (n : ℕ) :
    a n = ((n : ℤ) ^ 2) / 10 - (((n : ℤ) - 1) ^ 2) / 10 := by
  unfold a
  have h1 : ((n : ℚ) ^ 2) / 10 = (((n : ℤ) ^ 2 : ℤ) : ℚ) / ((10 : ℕ) : ℚ) := by push_cast; ring
  have h2 : (((n : ℚ) - 1) ^ 2) / 10 = ((((n : ℤ) - 1) ^ 2 : ℤ) : ℚ) / ((10 : ℕ) : ℚ) := by
    push_cast; ring
  rw [h1, h2, Rat.floor_intCast_div_natCast, Rat.floor_intCast_div_natCast]
  rfl

lemma OMA.a_add (n : ℕ) : a (n + 10) = a n + 2 := by
  rw [OMA.a_int, OMA.a_int]
  push_cast
  have e1 : ((n : ℤ) + 10) ^ 2 = (n : ℤ) ^ 2 + 10 * (2 * n + 10) := by ring
  have e2 : ((n : ℤ) + 10 - 1) ^ 2 = ((n : ℤ) - 1) ^ 2 + 10 * (2 * n + 8) := by ring
  rw [e1, e2, Int.add_mul_ediv_left _ _ (by norm_num), Int.add_mul_ediv_left _ _ (by norm_num)]
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a134119.main := by
  have hL : PowerSeries.mk a * (X ^ 11 - X ^ 10 - X + 1 : PowerSeries ℤ)
      = PowerSeries.mk a * X ^ 11 - PowerSeries.mk a * X ^ 10 - PowerSeries.mk a * X ^ 1
        + PowerSeries.mk a := by ring
  have hR : (X ^ 4 * (X ^ 4 + 1) : PowerSeries ℤ) = X ^ 8 + X ^ 4 := by ring
  rw [hL, hR]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  rcases Nat.lt_or_ge n 11 with h | h
  · interval_cases n <;> simp [OMA.a_int]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    have h1 : 11 + m - 10 = m + 1 := by omega
    have h2 : 11 + m - 1 = m + 10 := by omega
    have h3 : 11 + m - 11 = m := by omega
    have h4 : 11 + m = m + 1 + 10 := by omega
    have e1 := OMA.a_add (m + 1)
    have e2 := OMA.a_add m
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), h1, h2, h3,
      if_neg (by omega), if_neg (by omega), h4, e1, e2]
    ring
