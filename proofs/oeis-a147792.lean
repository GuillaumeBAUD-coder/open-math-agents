import OMAStatements.S_oeis_a147792

namespace OMA.P147792

open OMA.S_oeis_a147792

lemma a_val (n : ℕ) (A B : ℤ) (hB : 0 < B) (hc : IsCoprime A B)
    (h : A * (16 * ((n : ℤ) + 1) ^ 2) = B * (((n : ℤ) + 1) ^ 2 - 1)) : (a n : ℤ) = B := by
  have hBq : (0 : ℚ) < (B : ℚ) := by exact_mod_cast hB
  have h' : (A : ℚ) * (16 * ((n : ℚ) + 1) ^ 2) = (B : ℚ) * (((n : ℚ) + 1) ^ 2 - 1) := by
    exact_mod_cast h
  have e : (1 : ℚ) / 16 - 1 / ((4 * n + 4 : ℕ) : ℚ) ^ 2 = (A : ℚ) / (B : ℚ) := by
    push_cast
    rw [div_sub_div _ _ (by norm_num) (by positivity),
      div_eq_div_iff (by positivity) (ne_of_gt hBq)]
    linear_combination (-16 : ℚ) * h'
  unfold a A061042
  rw [e]
  exact Rat.den_div_eq_of_coprime hB (Int.isCoprime_iff_gcd_eq_one.mp hc)

lemma a_even (n : ℕ) (h : n % 2 = 1) : (a n : ℤ) = 16 * ((n : ℤ) + 1) ^ 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, n = 2 * t + 1 := ⟨n / 2, by omega⟩
  have h2 : IsCoprime (4 * ((t : ℤ) + 1) ^ 2 - 1) 2 := ⟨-1, 2 * ((t : ℤ) + 1) ^ 2, by ring⟩
  have ht : IsCoprime (4 * ((t : ℤ) + 1) ^ 2 - 1) ((t : ℤ) + 1) :=
    ⟨-1, 4 * ((t : ℤ) + 1), by ring⟩
  have hc : IsCoprime (4 * ((t : ℤ) + 1) ^ 2 - 1) (2 ^ 6 * ((t : ℤ) + 1) ^ 2) :=
    (h2.pow_right).mul_right (ht.pow_right)
  have hB : (0 : ℤ) < 2 ^ 6 * ((t : ℤ) + 1) ^ 2 := by positivity
  rw [a_val (2 * t + 1) _ _ hB hc (by push_cast; ring)]
  push_cast
  ring

lemma a_one (n : ℕ) (h : n % 8 = 0 ∨ n % 8 = 6) : (a n : ℤ) = ((n : ℤ) + 1) ^ 2 := by
  rcases h with h | h
  · obtain ⟨s, rfl⟩ : ∃ s, n = 8 * s := ⟨n / 8, by omega⟩
    have hc : IsCoprime (4 * (s : ℤ) ^ 2 + s) ((8 * (s : ℤ) + 1) ^ 2) := ⟨-16, 1, by ring⟩
    have hB : (0 : ℤ) < (8 * (s : ℤ) + 1) ^ 2 := by positivity
    rw [a_val (8 * s) _ _ hB hc (by push_cast; ring)]
    push_cast
    ring
  · obtain ⟨s, rfl⟩ : ∃ s, n = 8 * s + 6 := ⟨n / 8, by omega⟩
    have hc : IsCoprime (4 * (s : ℤ) ^ 2 + 7 * s + 3) ((8 * (s : ℤ) + 7) ^ 2) :=
      ⟨-16, 1, by ring⟩
    have hB : (0 : ℤ) < (8 * (s : ℤ) + 7) ^ 2 := by positivity
    rw [a_val (8 * s + 6) _ _ hB hc (by push_cast; ring)]
    push_cast
    ring

lemma a_three (n : ℕ) (h : n % 8 = 2 ∨ n % 8 = 4) : (a n : ℤ) = 2 * ((n : ℤ) + 1) ^ 2 := by
  rcases h with h | h
  · obtain ⟨s, rfl⟩ : ∃ s, n = 8 * s + 2 := ⟨n / 8, by omega⟩
    have h1 : IsCoprime (2 * (4 * (s : ℤ) ^ 2 + 3 * s) + 1) ((8 * (s : ℤ) + 3) ^ 2) :=
      ⟨-8, 1, by ring⟩
    have h2 : IsCoprime (2 * (4 * (s : ℤ) ^ 2 + 3 * s) + 1) 2 :=
      ⟨1, -(4 * (s : ℤ) ^ 2 + 3 * s), by ring⟩
    have hc := h2.mul_right h1
    have hB : (0 : ℤ) < 2 * (8 * (s : ℤ) + 3) ^ 2 := by positivity
    rw [a_val (8 * s + 2) _ _ hB hc (by push_cast; ring)]
    push_cast
    ring
  · obtain ⟨s, rfl⟩ : ∃ s, n = 8 * s + 4 := ⟨n / 8, by omega⟩
    have h1 : IsCoprime (2 * (4 * (s : ℤ) ^ 2 + 5 * s + 1) + 1) ((8 * (s : ℤ) + 5) ^ 2) :=
      ⟨-8, 1, by ring⟩
    have h2 : IsCoprime (2 * (4 * (s : ℤ) ^ 2 + 5 * s + 1) + 1) 2 :=
      ⟨1, -(4 * (s : ℤ) ^ 2 + 5 * s + 1), by ring⟩
    have hc := h2.mul_right h1
    have hB : (0 : ℤ) < 2 * (8 * (s : ℤ) + 5) ^ 2 := by positivity
    rw [a_val (8 * s + 4) _ _ hB hc (by push_cast; ring)]
    push_cast
    ring

lemma rec0 (k : ℕ) (h : k % 8 = 0) :
    (a (k + 18) : ℤ) = 3 * (a (k + 16) : ℤ) - 6 * (a (k + 14) : ℤ) + 10 * (a (k + 12) : ℤ)
      - 12 * (a (k + 10) : ℤ) + 12 * (a (k + 8) : ℤ) - 10 * (a (k + 6) : ℤ)
      + 6 * (a (k + 4) : ℤ) - 3 * (a (k + 2) : ℤ) + (a k : ℤ) := by
  rw [a_three (k + 18) (by omega),
    a_one (k + 16) (by omega),
    a_one (k + 14) (by omega),
    a_three (k + 12) (by omega),
    a_three (k + 10) (by omega),
    a_one (k + 8) (by omega),
    a_one (k + 6) (by omega),
    a_three (k + 4) (by omega),
    a_three (k + 2) (by omega),
    a_one k (by omega)]
  push_cast
  ring

lemma rec1 (k : ℕ) (h : k % 8 = 1) :
    (a (k + 18) : ℤ) = 3 * (a (k + 16) : ℤ) - 6 * (a (k + 14) : ℤ) + 10 * (a (k + 12) : ℤ)
      - 12 * (a (k + 10) : ℤ) + 12 * (a (k + 8) : ℤ) - 10 * (a (k + 6) : ℤ)
      + 6 * (a (k + 4) : ℤ) - 3 * (a (k + 2) : ℤ) + (a k : ℤ) := by
  rw [a_even (k + 18) (by omega),
    a_even (k + 16) (by omega),
    a_even (k + 14) (by omega),
    a_even (k + 12) (by omega),
    a_even (k + 10) (by omega),
    a_even (k + 8) (by omega),
    a_even (k + 6) (by omega),
    a_even (k + 4) (by omega),
    a_even (k + 2) (by omega),
    a_even k (by omega)]
  push_cast
  ring

lemma rec2 (k : ℕ) (h : k % 8 = 2) :
    (a (k + 18) : ℤ) = 3 * (a (k + 16) : ℤ) - 6 * (a (k + 14) : ℤ) + 10 * (a (k + 12) : ℤ)
      - 12 * (a (k + 10) : ℤ) + 12 * (a (k + 8) : ℤ) - 10 * (a (k + 6) : ℤ)
      + 6 * (a (k + 4) : ℤ) - 3 * (a (k + 2) : ℤ) + (a k : ℤ) := by
  rw [a_three (k + 18) (by omega),
    a_three (k + 16) (by omega),
    a_one (k + 14) (by omega),
    a_one (k + 12) (by omega),
    a_three (k + 10) (by omega),
    a_three (k + 8) (by omega),
    a_one (k + 6) (by omega),
    a_one (k + 4) (by omega),
    a_three (k + 2) (by omega),
    a_three k (by omega)]
  push_cast
  ring

lemma rec3 (k : ℕ) (h : k % 8 = 3) :
    (a (k + 18) : ℤ) = 3 * (a (k + 16) : ℤ) - 6 * (a (k + 14) : ℤ) + 10 * (a (k + 12) : ℤ)
      - 12 * (a (k + 10) : ℤ) + 12 * (a (k + 8) : ℤ) - 10 * (a (k + 6) : ℤ)
      + 6 * (a (k + 4) : ℤ) - 3 * (a (k + 2) : ℤ) + (a k : ℤ) := by
  rw [a_even (k + 18) (by omega),
    a_even (k + 16) (by omega),
    a_even (k + 14) (by omega),
    a_even (k + 12) (by omega),
    a_even (k + 10) (by omega),
    a_even (k + 8) (by omega),
    a_even (k + 6) (by omega),
    a_even (k + 4) (by omega),
    a_even (k + 2) (by omega),
    a_even k (by omega)]
  push_cast
  ring

lemma rec4 (k : ℕ) (h : k % 8 = 4) :
    (a (k + 18) : ℤ) = 3 * (a (k + 16) : ℤ) - 6 * (a (k + 14) : ℤ) + 10 * (a (k + 12) : ℤ)
      - 12 * (a (k + 10) : ℤ) + 12 * (a (k + 8) : ℤ) - 10 * (a (k + 6) : ℤ)
      + 6 * (a (k + 4) : ℤ) - 3 * (a (k + 2) : ℤ) + (a k : ℤ) := by
  rw [a_one (k + 18) (by omega),
    a_three (k + 16) (by omega),
    a_three (k + 14) (by omega),
    a_one (k + 12) (by omega),
    a_one (k + 10) (by omega),
    a_three (k + 8) (by omega),
    a_three (k + 6) (by omega),
    a_one (k + 4) (by omega),
    a_one (k + 2) (by omega),
    a_three k (by omega)]
  push_cast
  ring

lemma rec5 (k : ℕ) (h : k % 8 = 5) :
    (a (k + 18) : ℤ) = 3 * (a (k + 16) : ℤ) - 6 * (a (k + 14) : ℤ) + 10 * (a (k + 12) : ℤ)
      - 12 * (a (k + 10) : ℤ) + 12 * (a (k + 8) : ℤ) - 10 * (a (k + 6) : ℤ)
      + 6 * (a (k + 4) : ℤ) - 3 * (a (k + 2) : ℤ) + (a k : ℤ) := by
  rw [a_even (k + 18) (by omega),
    a_even (k + 16) (by omega),
    a_even (k + 14) (by omega),
    a_even (k + 12) (by omega),
    a_even (k + 10) (by omega),
    a_even (k + 8) (by omega),
    a_even (k + 6) (by omega),
    a_even (k + 4) (by omega),
    a_even (k + 2) (by omega),
    a_even k (by omega)]
  push_cast
  ring

lemma rec6 (k : ℕ) (h : k % 8 = 6) :
    (a (k + 18) : ℤ) = 3 * (a (k + 16) : ℤ) - 6 * (a (k + 14) : ℤ) + 10 * (a (k + 12) : ℤ)
      - 12 * (a (k + 10) : ℤ) + 12 * (a (k + 8) : ℤ) - 10 * (a (k + 6) : ℤ)
      + 6 * (a (k + 4) : ℤ) - 3 * (a (k + 2) : ℤ) + (a k : ℤ) := by
  rw [a_one (k + 18) (by omega),
    a_one (k + 16) (by omega),
    a_three (k + 14) (by omega),
    a_three (k + 12) (by omega),
    a_one (k + 10) (by omega),
    a_one (k + 8) (by omega),
    a_three (k + 6) (by omega),
    a_three (k + 4) (by omega),
    a_one (k + 2) (by omega),
    a_one k (by omega)]
  push_cast
  ring

lemma rec7 (k : ℕ) (h : k % 8 = 7) :
    (a (k + 18) : ℤ) = 3 * (a (k + 16) : ℤ) - 6 * (a (k + 14) : ℤ) + 10 * (a (k + 12) : ℤ)
      - 12 * (a (k + 10) : ℤ) + 12 * (a (k + 8) : ℤ) - 10 * (a (k + 6) : ℤ)
      + 6 * (a (k + 4) : ℤ) - 3 * (a (k + 2) : ℤ) + (a k : ℤ) := by
  rw [a_even (k + 18) (by omega),
    a_even (k + 16) (by omega),
    a_even (k + 14) (by omega),
    a_even (k + 12) (by omega),
    a_even (k + 10) (by omega),
    a_even (k + 8) (by omega),
    a_even (k + 6) (by omega),
    a_even (k + 4) (by omega),
    a_even (k + 2) (by omega),
    a_even k (by omega)]
  push_cast
  ring

end OMA.P147792

open OMA.S_oeis_a147792 OMA.P147792 in
theorem OMA.solution : type_of% @OMA.S_oeis_a147792.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 18 := ⟨n - 18, by omega⟩
  have e2 : k + 18 - 2 = k + 16 := by omega
  have e4 : k + 18 - 4 = k + 14 := by omega
  have e6 : k + 18 - 6 = k + 12 := by omega
  have e8 : k + 18 - 8 = k + 10 := by omega
  have e10 : k + 18 - 10 = k + 8 := by omega
  have e12 : k + 18 - 12 = k + 6 := by omega
  have e14 : k + 18 - 14 = k + 4 := by omega
  have e16 : k + 18 - 16 = k + 2 := by omega
  have e18 : k + 18 - 18 = k := by omega
  rw [e2, e4, e6, e8, e10, e12, e14, e16, e18]
  have hk : k % 8 = 0 ∨ k % 8 = 1 ∨ k % 8 = 2 ∨ k % 8 = 3 ∨ k % 8 = 4 ∨ k % 8 = 5 ∨ k % 8 = 6
      ∨ k % 8 = 7 := by omega
  rcases hk with h | h | h | h | h | h | h | h
  · exact rec0 k h
  · exact rec1 k h
  · exact rec2 k h
  · exact rec3 k h
  · exact rec4 k h
  · exact rec5 k h
  · exact rec6 k h
  · exact rec7 k h
