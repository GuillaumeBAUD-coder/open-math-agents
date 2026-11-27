import OMAReductions.R_Green95_green_95_variants_three_palindromes_R1

-- Step Green95.green_95.variants.three_palindromes.R1.H1: hypothesis H1 of reduction Green95.green_95.variants.three_palindromes.R1
-- Credit: @DeepDuke
-- H1 := ∀ g : ℕ, 5 ≤ g → ∀ n : ℕ, 0 < n → n < g →     ∃ p q r, IsPalindrome g p ∧ IsPalindrome g q ∧ IsPalindrome g r ∧ p + q + r = n  /-- The induction step: every `n ≥ g` is a sum of three base-`g` palindromes. -/

theorem OMA.solution : OMA.R_Green95_green_95_variants_three_palindromes_R1.H1 := by
  intro g hg n hn hng
  refine ⟨n, 0, 0, ?_, Green95.isPalindrome_zero g, Green95.isPalindrome_zero g, by omega⟩
  simp [Green95.IsPalindrome, Nat.digits_of_lt g n hn.ne' hng]

