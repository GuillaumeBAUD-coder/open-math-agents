import OMAStatements.S_oeis_a016789

namespace OMA.S_oeis_a016789

end OMA.S_oeis_a016789

open OMA.S_oeis_a016789 in
theorem OMA.solution : type_of% @OMA.S_oeis_a016789.main := by
  intro y
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨9 * n ^ 3 + 18 * n ^ 2 + 12 * n + 2, ?_⟩
    have hy : y = a n := hn.symm
    subst hy
    show ((a n : ℕ) : ℤ) ^ 3 = 3 * (9 * n ^ 3 + 18 * n ^ 2 + 12 * n + 2) + 2
    simp only [a]
    push_cast
    ring
  · rintro ⟨k, hk⟩
    obtain h0 | h1 | h2 : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by omega
    · exfalso
      have hy : y = y / 3 * 3 := by omega
      have hk2 : ((y / 3 * 3 : ℕ) : ℤ) ^ 3 = 3 * k + 2 := by rw [hy] at hk; exact hk
      have hexp : ((y / 3 * 3 : ℕ) : ℤ) ^ 3 = 3 * (9 * ((y / 3 : ℕ) : ℤ) ^ 3) := by
        push_cast; ring
      rw [hexp] at hk2
      omega
    · exfalso
      have hy : y = y / 3 * 3 + 1 := by omega
      have hk2 : ((y / 3 * 3 + 1 : ℕ) : ℤ) ^ 3 = 3 * k + 2 := by rw [hy] at hk; exact hk
      have hexp : ((y / 3 * 3 + 1 : ℕ) : ℤ) ^ 3 =
          3 * (9 * ((y / 3 : ℕ) : ℤ) ^ 3 + 9 * ((y / 3 : ℕ) : ℤ) ^ 2 + 3 * ((y / 3 : ℕ) : ℤ)) + 1 := by
        push_cast; ring
      rw [hexp] at hk2
      omega
    · refine ⟨y / 3, ?_⟩
      show a (y / 3) = y
      simp only [a]
      omega
