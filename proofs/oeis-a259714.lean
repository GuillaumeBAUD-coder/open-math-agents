import OMAStatements.S_oeis_a259714

-- Problem: A259714: a(n) = Sum_{k=1..n-1}((k mod 5)*a(n-k)), a(1) = 1.
-- Upstream: formal-conjectures statements/oeis-a259714.lean:0 (declaration OMA.S_oeis_a259714.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a259714

open OMA.S_oeis_a259714

lemma a_succ (n : ℕ) (hn : n ≠ 0) :
    a (n + 1) = ∑ j ∈ Finset.range n, ((j + 1) % 5) * a (n - j) := by
  rw [a, if_neg hn]

lemma rec5 : ∀ n : ℕ, 6 < n →
    a n = a (n - 1) + 2 * a (n - 2) + 3 * a (n - 3) + 4 * a (n - 4) + a (n - 5) := by
  intro N hN
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 7 := ⟨N - 7, by omega⟩
  rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
    show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega,
    show m + 7 - 5 = m + 2 by omega]
  rw [show m + 7 = (m + 6) + 1 by ring, a_succ (m + 6) (by omega),
    show m + 6 = 5 + (m + 1) by ring, Finset.sum_range_add]
  rw [show m + 2 = (m + 1) + 1 by ring, a_succ (m + 1) (by omega)]
  have hshift : ∑ x ∈ Finset.range (m + 1), ((5 + x + 1) % 5) * a (5 + (m + 1) - (5 + x)) =
      ∑ x ∈ Finset.range (m + 1), ((x + 1) % 5) * a (m + 1 - x) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [show (5 + x + 1) % 5 = (x + 1) % 5 by omega, show 5 + (m + 1) - (5 + x) = m + 1 - x by omega]
  rw [hshift]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  rw [show 5 + m = m + 5 by ring, show 5 + (m + 1) - 2 = m + 4 by omega,
    show 5 + (m + 1) - 3 = m + 3 by omega]

lemma coeff_Xpow (f : ℕ → ℚ) (k d : ℕ) :
    PowerSeries.coeff d (PowerSeries.mk f * PowerSeries.X ^ k) = if k ≤ d then f (d - k) else 0 := by
  rw [PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk]

lemma a0 : a 0 = 0 := by rw [a]
lemma a1 : a 1 = 1 := by rw [a, if_pos rfl]
lemma a2 : a 2 = 1 := by rw [a_succ 1 (by omega)]; simp [a1]
lemma a3 : a 3 = 3 := by rw [a_succ 2 (by omega)]; simp [Finset.sum_range_succ, a1, a2]
lemma a4 : a 4 = 8 := by rw [a_succ 3 (by omega)]; simp [Finset.sum_range_succ, a1, a2, a3]
lemma a5 : a 5 = 21 := by rw [a_succ 4 (by omega)]; simp [Finset.sum_range_succ, a1, a2, a3, a4]
lemma a6 : a 6 = 50 := by
  rw [a_succ 5 (by omega)]; simp [Finset.sum_range_succ, a1, a2, a3, a4, a5]

open PowerSeries in
lemma gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((X + 1) * (X ^ 4 + 3 * X ^ 3 + 2 * X - 1)) =
    X * (X - 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) := by
  have hden : ((X + 1) * (X ^ 4 + 3 * X ^ 3 + 2 * X - 1) : PowerSeries ℚ) =
      X ^ 5 + C (4 : ℚ) * X ^ 4 + C (3 : ℚ) * X ^ 3 + C (2 : ℚ) * X ^ 2 + X ^ 1 - X ^ 0 := by
    simp only [map_ofNat]
    ring
  have hnum : (X * (X - 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) : PowerSeries ℚ) = X ^ 6 - X ^ 1 := by
    ring
  rw [hden, hnum]
  ext d
  have e : PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 5 + C (4 : ℚ) * X ^ 4 + C (3 : ℚ) * X ^ 3 +
      C (2 : ℚ) * X ^ 2 + X ^ 1 - X ^ 0) =
      PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 5 +
        C (4 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4) +
        C (3 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3) +
        C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2) +
        PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1 - PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 0 := by
    ring
  rw [e]
  simp only [map_sub, map_add, coeff_C_mul, coeff_Xpow, coeff_X_pow]
  have q0 : (a 0 : ℚ) = 0 := by exact_mod_cast a0
  have q1 : (a 1 : ℚ) = 1 := by exact_mod_cast a1
  have q2 : (a 2 : ℚ) = 1 := by exact_mod_cast a2
  have q3 : (a 3 : ℚ) = 3 := by exact_mod_cast a3
  have q4 : (a 4 : ℚ) = 8 := by exact_mod_cast a4
  have q5 : (a 5 : ℚ) = 21 := by exact_mod_cast a5
  have q6 : (a 6 : ℚ) = 50 := by exact_mod_cast a6
  rcases d with _ | _ | _ | _ | _ | _ | _ | m
  · simp [q0]
  · simp [q0, q1]
  · simp [q0, q1, q2]
  · simp [q0, q1, q2, q3] <;> norm_num
  · simp [q0, q1, q2, q3, q4] <;> norm_num
  · simp [q0, q1, q2, q3, q4, q5] <;> norm_num
  · simp [q0, q1, q2, q3, q4, q5, q6] <;> norm_num
  · have h := rec5 (m + 7) (by omega)
    rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
      show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega,
      show m + 7 - 5 = m + 2 by omega] at h
    have hq : (a (m + 7) : ℚ) = a (m + 6) + 2 * a (m + 5) + 3 * a (m + 4) + 4 * a (m + 3) +
        a (m + 2) := by exact_mod_cast h
    have e0 : ¬ (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 6) := by omega
    have e1 : ¬ (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 1) := by omega
    simp only [if_pos (show 5 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega),
      if_pos (show 4 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega),
      if_pos (show 3 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega),
      if_pos (show 2 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega),
      if_pos (show 1 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega),
      if_pos (show 0 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega), if_neg e0, if_neg e1]
    rw [show m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 2 by omega,
      show m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 3 by omega,
      show m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 4 by omega,
      show m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 5 by omega,
      show m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 6 by omega,
      show m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 0 = m + 7 by omega]
    linear_combination (-1 : ℚ) * hq

open PowerSeries in
lemma solve : (∀ n : ℕ, 6 < n →
    a n = a (n - 1) + 2 * a (n - 2) + 3 * a (n - 3) + 4 * a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X + 1) * (X ^ 4 + 3 * X ^ 3 + 2 * X - 1)) =
      X * (X - 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) := ⟨rec5, gf⟩

end OMA.P_oeis_a259714

theorem OMA.solution : type_of% @OMA.S_oeis_a259714.main := OMA.P_oeis_a259714.solve
