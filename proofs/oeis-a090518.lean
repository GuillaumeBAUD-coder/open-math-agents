import OMAStatements.S_oeis_a090518

-- Problem: A090518, no term is zero.
-- Credit: @bnb9001

open OMA.S_oeis_a090518 in
theorem OMA.solution : type_of% @OMA.S_oeis_a090518.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hmem : 5 * 10 ^ m ∈ {k : ℕ | (10 ^ (m + 1) / k).Prime} := by
    show (10 ^ (m + 1) / (5 * 10 ^ m)).Prime
    have : 10 ^ (m + 1) = 2 * (5 * 10 ^ m) := by ring
    rw [this, Nat.mul_div_cancel _ (by positivity)]
    exact Nat.prime_two
  have hs : (10 ^ (m + 1) / b (m + 1)).Prime := Nat.sInf_mem ⟨_, hmem⟩
  have hb : b (m + 1) ≠ 0 := by
    intro h0
    rw [h0] at hs
    exact Nat.not_prime_zero (by simpa using hs)
  unfold a
  rw [if_neg hb]
  exact hs.ne_zero
