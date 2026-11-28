import OMAStatements.S_oeis_a123167

open OMA.S_oeis_a123167 in
/-- `4/n - 2/n^2 = (4n-2)/n^2`. For `n = 2j+1` this is `(8j+2)/(2j+1)^2` with coprime parts; for
`n = 2j` it is `(4j-1)/(2j^2)` with coprime parts. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a123167.main := by
  intro n hn
  have key : ∀ p q : ℤ, 0 < q → IsCoprime p q → (p / q : ℚ).num = p := by
    intro p q hq hpq
    apply Rat.num_div_eq_of_coprime hq
    have := Int.isCoprime_iff_gcd_eq_one.mp hpq
    exact this
  rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have hj : 1 ≤ j := by omega
    have ha : a (j + j) = 4 * j - 1 := by
      unfold a; rw [if_neg (by omega)]; congr 1; omega
    rw [ha]
    have e : (4 / ((j + j : ℕ) : ℚ) - 2 / ((j + j : ℕ) : ℚ) ^ 2) =
        (((4 * j - 1 : ℕ) : ℤ) : ℚ) / ((2 * j ^ 2 : ℕ) : ℤ) := by
      have hj' : (j : ℚ) ≠ 0 := by positivity
      push_cast [show 1 ≤ 4 * j by omega]
      field_simp
      ring
    rw [e]
    apply key
    · positivity
    · push_cast [show 1 ≤ 4 * j by omega]
      have h1 : IsCoprime (4 * (j : ℤ) - 1) 2 := ⟨-1, 2 * j, by ring⟩
      have h2 : IsCoprime (4 * (j : ℤ) - 1) j := ⟨-1, 4, by ring⟩
      exact h1.mul_right (h2.pow_right)
  · have ha : a (2 * j + 1) = 8 * j + 2 := by
      unfold a; rw [if_pos (by omega)]; omega
    rw [ha]
    have e : (4 / ((2 * j + 1 : ℕ) : ℚ) - 2 / ((2 * j + 1 : ℕ) : ℚ) ^ 2) =
        (((8 * j + 2 : ℕ) : ℤ) : ℚ) / (((2 * j + 1) ^ 2 : ℕ) : ℤ) := by
      have hj' : (2 * (j : ℚ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    rw [e]
    apply key
    · positivity
    · push_cast
      have h1 : IsCoprime (8 * (j : ℤ) + 2) (2 * j + 1) := ⟨j, 1 - 4 * j, by ring⟩
      exact h1.pow_right
