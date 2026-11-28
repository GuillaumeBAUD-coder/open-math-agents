import OMAStatements.S_oeis_a098664

namespace OMA.P098664

open OMA.S_oeis_a098664

lemma a_even (k : ℕ) :
    a (2 * k) = ((2 * k).factorial : ℚ) * 4 ^ k / ((k.factorial : ℚ) ^ 2) := by
  have h1 : Even (2 * k) := even_two_mul k
  have h2 : ¬ Odd (2 * k) := by
    rw [Nat.not_odd_iff_even]
    exact h1
  have h3 : 2 * k / 2 = k := by omega
  have h4 : (2 : ℚ) ^ (2 * k) = 4 ^ k := by
    rw [pow_mul]
    norm_num
  unfold a i0 i1
  rw [if_pos h1, if_neg h2, h3, h4]
  ring

lemma a_odd (k : ℕ) :
    a (2 * k + 1) = ((2 * k + 1).factorial : ℚ) * 4 ^ k
      / ((k.factorial : ℚ) * ((k + 1).factorial : ℚ)) := by
  have h1 : Odd (2 * k + 1) := odd_two_mul_add_one k
  have h2 : ¬ Even (2 * k + 1) := by
    rw [Nat.not_even_iff_odd]
    exact h1
  have h3 : (2 * k + 1 - 1) / 2 = k := by omega
  have h5 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  have h4 : (2 : ℚ) ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  unfold a i0 i1
  rw [if_pos h1, if_neg h2, h3, h5, h4]
  ring

lemma fact_ne (k : ℕ) : (k.factorial : ℚ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero k

end OMA.P098664

open OMA.S_oeis_a098664 OMA.P098664 in
theorem OMA.solution : type_of% @OMA.S_oeis_a098664.main := by
  intro n hn
  have hk := fact_ne
  rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    have e1 : 2 * (k + 2) - 1 = 2 * (k + 1) + 1 := by omega
    have e2 : 2 * (k + 2) - 2 = 2 * (k + 1) := by omega
    have e3 : 2 * (k + 2) - 3 = 2 * k + 1 := by omega
    rw [e1, e2, e3, a_even, a_even, a_odd, a_odd]
    have f1 : 2 * (k + 2) = 2 * k + 3 + 1 := by ring
    have f2 : 2 * (k + 1) + 1 = 2 * k + 2 + 1 := by ring
    have f3 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [f1, f2, f3]
    simp only [Nat.factorial_succ]
    push_cast
    have h0 := hk k
    have h1 := hk (2 * k)
    have p1 : (k : ℚ) + 1 ≠ 0 := by positivity
    have p2 : (k : ℚ) + 1 + 1 ≠ 0 := by positivity
    field_simp
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have e1 : 2 * (k + 1) + 1 - 1 = 2 * (k + 1) := by omega
    have e2 : 2 * (k + 1) + 1 - 2 = 2 * k + 1 := by omega
    have e3 : 2 * (k + 1) + 1 - 3 = 2 * k := by omega
    rw [e1, e2, e3, a_even, a_even, a_odd, a_odd]
    have f1 : 2 * (k + 1) + 1 = 2 * k + 2 + 1 := by ring
    have f3 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [f1, f3]
    simp only [Nat.factorial_succ]
    push_cast
    have h0 := hk k
    have h1 := hk (2 * k)
    have p1 : (k : ℚ) + 1 ≠ 0 := by positivity
    have p2 : (k : ℚ) + 1 + 1 ≠ 0 := by positivity
    field_simp
    ring
