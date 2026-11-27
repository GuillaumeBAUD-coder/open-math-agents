import OMAReductions.R_OeisA238585_conjecture_1_R1

-- Step OeisA238585.conjecture_1.R1.H1: hypothesis H1 of reduction OeisA238585.conjecture_1.R1
-- Credit: @NoahPuckett-IO
-- The divisors of 6 are 1, 2, 3, 6; evaluate the count directly: 25, 153, 169 and 265 are composite.

theorem OMA.solution : OMA.R_OeisA238585_conjecture_1_R1.H1 := by
  intro n hn
  have h13 : Nat.nth Nat.Prime 5 = 13 := by
    have h : Nat.count Nat.Prime 13 = 5 := by decide
    rw [← h]
    exact Nat.nth_count (by norm_num)
  have hmem : n ∈ Nat.divisors 6 := Nat.mem_divisors.2 ⟨hn, by norm_num⟩
  have hd : Nat.divisors 6 = {1, 2, 3, 6} := by decide
  rw [hd] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl <;>
    simp [OeisA238585.a] <;> intro x h1 h2 hp <;> interval_cases x <;>
    first
    | (norm_num [Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five,
        Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven, h13]; done)
    | exact absurd hp (by norm_num)
