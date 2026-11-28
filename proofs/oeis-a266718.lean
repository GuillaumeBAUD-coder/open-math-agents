import OMAStatements.S_oeis_a266718

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: under Rule 59 a cell is ON next iff it is OFF now, or its left neighbour is OFF and its
-- right neighbour is ON. By induction, row 2k+1 is everything but cell k and row 2k+2 is exactly
-- the cells k and k+1. So a(2k+1) = 2^(4k+3) - 1 - 2^(k+1) and a(2k+2) = 3 * 2^(k+1); the
-- recurrence follows by ring, and the generating function from A * D = N coefficientwise.

namespace OMA.S_oeis_a266718

open PowerSeries

lemma rule59 (s : ℤ → Bool) (x : ℤ) :
    step 59 s x = (!(s x) || (!(s (x - 1)) && s (x + 1))) := by
  unfold step
  cases s (x - 1) <;> cases s x <;> cases s (x + 1) <;> decide

lemma rows (k : ℕ) :
    (∀ i : ℤ, state 59 (2 * k + 1) i = decide (i ≠ k)) ∧
    (∀ i : ℤ, state 59 (2 * k + 2) i = decide (i = k ∨ i = k + 1)) := by
  have odd_of_even : ∀ k : ℕ, (∀ i : ℤ, state 59 (2 * k) i = decide (i = (k : ℤ) - 1 ∨ i = k)) →
      ∀ i : ℤ, state 59 (2 * k + 1) i = decide (i ≠ k) := by
    intro k h i
    show step 59 (state 59 (2 * k)) i = _
    rw [rule59, h, h, h]
    by_cases h1 : i = k
    · subst h1; simp
    by_cases h2 : i = (k : ℤ) - 1
    · subst h2; simp <;> omega
    simp [h1, h2] <;> omega
  induction k with
  | zero =>
    have h1 : ∀ i : ℤ, state 59 1 i = decide (i ≠ 0) := by
      intro i
      show step 59 (state 59 0) i = _
      rw [rule59]
      simp only [state]
      by_cases h0 : i = 0
      · subst h0; decide
      by_cases hm : i = -1
      · subst hm; decide
      by_cases hp : i = 1
      · subst hp; decide
      have h2 : i - 1 ≠ 0 := by omega
      have h3 : i + 1 ≠ 0 := by omega
      simp [h0, h2, h3]
    refine ⟨by simpa using h1, ?_⟩
    intro i
    show step 59 (state 59 1) i = _
    rw [rule59, h1, h1, h1]
    by_cases h0 : i = 0
    · subst h0; decide
    by_cases ho : i = 1
    · subst ho; decide
    have h2 : i - 1 ≠ 0 := by omega
    simp [h0, ho, h2] <;> omega
  | succ k ih =>
    have hodd : ∀ i : ℤ, state 59 (2 * (k + 1) + 1) i = decide (i ≠ ((k + 1 : ℕ) : ℤ)) := by
      apply odd_of_even
      intro i
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, ih.2 i]
      push_cast
      congr 1
      apply propext
      constructor <;> intro h <;> rcases h with h | h <;> [left; right; left; right] <;> linarith
    refine ⟨hodd, ?_⟩
    intro i
    show step 59 (state 59 (2 * (k + 1) + 1)) i = _
    rw [rule59, hodd, hodd, hodd]
    push_cast
    by_cases h1 : i = (k : ℤ) + 1
    · subst h1; simp
    by_cases h2 : i = (k : ℤ) + 1 + 1
    · subst h2; simp <;> omega
    simp [h1, h2] <;> omega

lemma geom2 (N : ℕ) : ∑ i ∈ Finset.range N, (2 : ℤ) ^ i = 2 ^ N - 1 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; ring

lemma a_odd (k : ℕ) : (a (2 * k + 1) : ℤ) = 2 ^ (4 * k + 3) - 1 - 2 ^ (k + 1) := by
  simp only [a, rowValue]
  push_cast
  have hs : ∀ i ∈ Finset.range (2 * (2 * k + 1) + 1),
      ((state 59 (2 * k + 1) (2 * (k : ℤ) + 1 - (i : ℤ))).toNat : ℤ) * 2 ^ i =
      2 ^ i - if i = k + 1 then 2 ^ i else 0 := by
    intro i _
    rw [(rows k).1]
    by_cases h : i = k + 1
    · subst h; push_cast; simp <;> ring
    · rw [if_neg h]
      simp <;> omega
  rw [Finset.sum_congr rfl hs, Finset.sum_sub_distrib, geom2, Finset.sum_ite_eq']
  rw [if_pos (by simp; omega)]
  ring_nf

lemma a_even (k : ℕ) : (a (2 * k + 2) : ℤ) = 3 * 2 ^ (k + 1) := by
  simp only [a, rowValue]
  push_cast
  have hs : ∀ i ∈ Finset.range (2 * (2 * k + 2) + 1),
      ((state 59 (2 * k + 2) (2 * (k : ℤ) + 2 - (i : ℤ))).toNat : ℤ) * 2 ^ i =
      (if i = k + 1 then 2 ^ i else 0) + (if i = k + 2 then 2 ^ i else 0) := by
    intro i _
    rw [(rows k).2]
    by_cases h : i = k + 1
    · subst h
      push_cast; simp <;> omega
    by_cases h2 : i = k + 2
    · subst h2
      push_cast; simp <;> omega
    rw [if_neg h, if_neg h2]
    simp <;> omega
  rw [Finset.sum_congr rfl hs, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  rw [if_pos (by simp; omega), if_pos (by simp; omega)]
  ring

lemma a0 : a 0 = 1 := by decide +kernel

theorem recur (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 19 * a (n - 2) - 50 * a (n - 4) + 32 * a (n - 6) := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
    rw [show 2 * (j + 4) = 2 * (j + 3) + 2 by ring, show 2 * (j + 3) + 2 - 2 = 2 * (j + 2) + 2 by omega,
      show 2 * (j + 3) + 2 - 4 = 2 * (j + 1) + 2 by omega,
      show 2 * (j + 3) + 2 - 6 = 2 * j + 2 by omega]
    rw [a_even, a_even, a_even, a_even]
    ring
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    rw [show 2 * (j + 3) + 1 - 2 = 2 * (j + 2) + 1 by omega,
      show 2 * (j + 3) + 1 - 4 = 2 * (j + 1) + 1 by omega,
      show 2 * (j + 3) + 1 - 6 = 2 * j + 1 by omega]
    rw [a_odd, a_odd, a_odd, a_odd]
    ring

theorem gf_mul : A * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2)) =
    (1 - 2 * X) * (1 + 7 * X + X ^ 2 + 30 * X ^ 3 + 8 * X ^ 4 - 32 * X ^ 5) := by
  have hL : A * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2)) =
      A - C (19 : ℚ) * (A * X ^ 2) + C (50 : ℚ) * (A * X ^ 4) - C (32 : ℚ) * (A * X ^ 6) := by
    simp only [map_ofNat]; ring
  have hR : ((1 - 2 * X) * (1 + 7 * X + X ^ 2 + 30 * X ^ 3 + 8 * X ^ 4 - 32 * X ^ 5) : ℚ⟦X⟧) =
      C (1 : ℚ) * X ^ 0 + C (5 : ℚ) * X ^ 1 - C (13 : ℚ) * X ^ 2 + C (28 : ℚ) * X ^ 3
        - C (52 : ℚ) * X ^ 4 - C (48 : ℚ) * X ^ 5 + C (64 : ℚ) * X ^ 6 := by
    simp only [map_ofNat, map_one]; ring
  rw [hL, hR, A]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_X_pow]
  rcases Nat.lt_or_ge n 7 with hn | hn
  · have q1 := a_odd 0
    have q2 := a_even 0
    have q3 := a_odd 1
    have q4 := a_even 1
    have q5 := a_odd 2
    have q6 := a_even 2
    norm_num at q1 q2 q3 q4 q5 q6
    have r1 : (a 1 : ℚ) = 5 := by exact_mod_cast q1
    have r2 : (a 2 : ℚ) = 6 := by exact_mod_cast q2
    have r3 : (a 3 : ℚ) = 123 := by exact_mod_cast q3
    have r4 : (a 4 : ℚ) = 12 := by exact_mod_cast q4
    have r5 : (a 5 : ℚ) = 2039 := by exact_mod_cast q5
    have r6 : (a 6 : ℚ) = 24 := by exact_mod_cast q6
    interval_cases n <;> simp [a0, r1, r2, r3, r4, r5, r6] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    have := recur (m + 7) (by omega)
    rw [show m + 7 - 2 = m + 5 by omega, show m + 7 - 4 = m + 3 by omega,
      show m + 7 - 6 = m + 1 by omega] at this
    have q : (a (m + 7) : ℚ) = 19 * a (m + 5) - 50 * a (m + 3) + 32 * a (m + 1) := by
      exact_mod_cast this
    rw [if_pos (show 2 ≤ m + 7 by omega), if_pos (show 4 ≤ m + 7 by omega),
      if_pos (show 6 ≤ m + 7 by omega),
      show m + 7 - 2 = m + 5 by omega, show m + 7 - 4 = m + 3 by omega,
      show m + 7 - 6 = m + 1 by omega]
    simp only [coeff_C, show m + 7 - 0 ≠ 0 by omega, show m + 7 - 1 ≠ 0 by omega,
      show m + 5 ≠ 0 by omega, show m + 7 - 3 ≠ 0 by omega, show m + 3 ≠ 0 by omega,
      show m + 7 - 5 ≠ 0 by omega, show m + 1 ≠ 0 by omega, if_false, ite_self]
    linarith

theorem gf : A = (1 - 2 * X) * (1 + 7 * X + X ^ 2 + 30 * X ^ 3 + 8 * X ^ 4 - 32 * X ^ 5) *
      ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2))⁻¹ := by
  rw [PowerSeries.eq_mul_inv_iff_mul_eq]
  · exact gf_mul
  · simp

end OMA.S_oeis_a266718

theorem OMA.solution : type_of% @OMA.S_oeis_a266718.main :=
  ⟨OMA.S_oeis_a266718.recur, OMA.S_oeis_a266718.gf⟩
