import OMAStatements.S_oeis_a266724

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: under Rule 59 a cell is ON next iff it is OFF now, or its left neighbour is OFF and its
-- right neighbour is ON. By induction, row 2k+1 is everything but cell k and row 2k+2 is exactly
-- the cells k and k+1. So a(2k+1) = 1 and a(2k+2) = 2(2k+2) - 1; the recurrence and the
-- generating function (A * D = N, then multiply by the inverse of D) follow coefficientwise.

namespace OMA.S_oeis_a266724

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

lemma a_odd (k : ℕ) : a (2 * k + 1) = 1 := by
  have hs : (Finset.range (2 * (2 * k + 1) + 1)).filter
      (fun i : ℕ => state 59 (2 * k + 1) (((2 * k + 1 : ℕ) : ℤ) - i) = false) = {k + 1} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, (rows k).1,
      decide_eq_false_iff_not, not_not]
    push_cast
    omega
  simp only [a, offCount]
  rw [hs, Finset.card_singleton]

lemma a_even (k : ℕ) : a (2 * k + 2) = 2 * (2 * k + 2) - 1 := by
  have hs : (Finset.range (2 * (2 * k + 2) + 1)).filter
      (fun i : ℕ => state 59 (2 * k + 2) (((2 * k + 2 : ℕ) : ℤ) - i) = false) =
      Finset.range (k + 1) ∪ Finset.Ico (k + 3) (4 * k + 5) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico,
      (rows k).2, decide_eq_false_iff_not]
    push_cast
    omega
  simp only [a, offCount]
  rw [hs, Finset.card_union_of_disjoint (by
    rw [Finset.disjoint_left]; intro x hx hy; simp at hx hy; omega),
    Finset.card_range, Nat.card_Ico]
  omega

lemma a_cases (n : ℕ) (hn : 0 < n) :
    (a n : ℤ) = if n % 2 = 1 then 1 else 2 * (n : ℤ) - 1 := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, a_even]
    rw [if_neg (show ¬ (2 * j + 2) % 2 = 1 by omega)]
    push_cast [show 1 ≤ 2 * (2 * j + 2) by omega]
    ring
  · rw [a_odd]; simp

theorem closed (n : ℕ) (hn : 0 < n) : (a n : ℤ) = (-1) ^ n * ((n : ℤ) - 1) + n := by
  rw [a_cases n hn]
  rcases Nat.even_or_odd n with he | ho
  · have : ¬ n % 2 = 1 := by have := Nat.even_iff.1 he; omega
    simp [this, he.neg_one_pow]; ring
  · have : n % 2 = 1 := Nat.odd_iff.1 ho
    simp [this, ho.neg_one_pow]

theorem recur (n : ℕ) (hn : 4 < n) : (a n : ℤ) = 2 * a (n - 2) - a (n - 4) := by
  rw [a_cases n (by omega), a_cases (n - 2) (by omega), a_cases (n - 4) (by omega)]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have h1 : ¬ (n - 2) % 2 = 1 := by omega
    have h2 : ¬ (n - 4) % 2 = 1 := by omega
    have h0 : ¬ n % 2 = 1 := by omega
    simp only [h0, h1, h2, if_false]
    push_cast [show 2 ≤ n by omega, show 4 ≤ n by omega]
    ring
  · have h1 : (n - 2) % 2 = 1 := by omega
    have h2 : (n - 4) % 2 = 1 := by omega
    simp [h, h1, h2]

lemma small : a 0 = 0 := by decide +kernel

theorem gf_mul : A * ((1 - X) ^ 2 * (1 + X) ^ 2) = X * (1 + 3 * X - X ^ 2 + X ^ 3) := by
  have hD : ((1 - X) ^ 2 * (1 + X) ^ 2 : ℚ⟦X⟧) = 1 - (X ^ 2 + X ^ 2) + X ^ 4 := by ring
  have hN : (X * (1 + 3 * X - X ^ 2 + X ^ 3) : ℚ⟦X⟧) =
      X ^ 1 + (X ^ 2 + X ^ 2 + X ^ 2) - X ^ 3 + X ^ 4 := by ring
  rw [hD, hN, A]
  ext n
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mul_X_pow', coeff_mk,
    coeff_X_pow]
  rcases Nat.lt_or_ge n 5 with hn | hn
  · have h1 := a_cases 1 (by norm_num)
    have h2 := a_cases 2 (by norm_num)
    have h3 := a_cases 3 (by norm_num)
    have h4 := a_cases 4 (by norm_num)
    norm_num at h1 h2 h3 h4
    have q1 : (a 1 : ℚ) = 1 := by exact_mod_cast h1
    have q2 : (a 2 : ℚ) = 3 := by exact_mod_cast h2
    have q3 : (a 3 : ℚ) = 1 := by exact_mod_cast h3
    have q4 : (a 4 : ℚ) = 7 := by exact_mod_cast h4
    interval_cases n <;> simp [small, q1, q2, q3, q4] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have := recur (m + 5) (by omega)
    rw [show m + 5 - 2 = m + 3 by omega, show m + 5 - 4 = m + 1 by omega] at this
    have q : (a (m + 5) : ℚ) = 2 * a (m + 3) - a (m + 1) := by exact_mod_cast this
    rw [if_pos (show 2 ≤ m + 5 by omega), if_pos (show 4 ≤ m + 5 by omega),
      show m + 5 - 2 = m + 3 by omega, show m + 5 - 4 = m + 1 by omega]
    simp only [show m + 5 ≠ 1 by omega, show m + 5 ≠ 2 by omega, show m + 5 ≠ 3 by omega,
      show m + 5 ≠ 4 by omega, if_false]
    linarith

theorem gf : A = X * (1 + 3 * X - X ^ 2 + X ^ 3) * ((1 - X) ^ 2 * (1 + X) ^ 2)⁻¹ := by
  rw [PowerSeries.eq_mul_inv_iff_mul_eq]
  · exact gf_mul
  · simp

end OMA.S_oeis_a266724

theorem OMA.solution : type_of% @OMA.S_oeis_a266724.main :=
  ⟨OMA.S_oeis_a266724.closed, OMA.S_oeis_a266724.recur, OMA.S_oeis_a266724.gf⟩
