import OMAStatements.S_oeis_a332446

namespace OMA.S_oeis_a332446



lemma f_even (n : ℕ) : A087808 (2 * n) = 2 * A087808 n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rw [A087808]
    simp
  · rw [A087808, dif_neg (by omega), if_pos (by omega), show 2 * n / 2 = n by omega]

lemma f_odd (n : ℕ) : A087808 (2 * n + 1) = A087808 n + 1 := by
  rw [A087808, dif_neg (by omega), if_neg (by omega), show (2 * n + 1) / 2 = n by omega]

/-- Controls from the entry: 3, 6, 11, 19, 28 are terms; 4, 5 are not. -/
example : A087808 (∑ d ∈ (3 : ℕ).divisors, d) = A087808 (2 * 3) ∧
    A087808 (∑ d ∈ (6 : ℕ).divisors, d) = A087808 (2 * 6) ∧
    A087808 (∑ d ∈ (28 : ℕ).divisors, d) = A087808 (2 * 28) ∧
    A087808 (∑ d ∈ (4 : ℕ).divisors, d) ≠ A087808 (2 * 4) ∧
    A087808 (∑ d ∈ (5 : ℕ).divisors, d) ≠ A087808 (2 * 5) := by
  decide +kernel

/-- McEachen's conjecture: every prime p == 3 (mod 8) is a term of A332446. -/
theorem conjecture : ∀ p : ℕ, p.Prime → p % 8 = 3 → InA332446 p := by
  intro p hp h3
  refine ⟨hp.pos, ?_⟩
  have hsum : ∑ d ∈ p.divisors, d = p + 1 := by
    rw [Nat.Prime.divisors hp, Finset.sum_pair (Nat.Prime.one_lt hp).ne]
    ring
  rw [hsum]
  obtain ⟨m, rfl⟩ : ∃ m, p = 8 * m + 3 := ⟨p / 8, by omega⟩
  rw [show 8 * m + 3 + 1 = 2 * (2 * (2 * m + 1)) by ring,
    show 2 * (8 * m + 3) = 2 * (2 * (2 * (2 * m) + 1) + 1) by ring]
  simp only [f_even, f_odd]
  ring

end OMA.S_oeis_a332446

theorem OMA.solution : type_of% @OMA.S_oeis_a332446.main :=
  OMA.S_oeis_a332446.conjecture
