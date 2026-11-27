import OMAReductions.R_Green95_green_95_variants_three_palindromes_R1

-- Step Green95.green_95.variants.three_palindromes.R1.H1: hypothesis H1 of reduction Green95.green_95.variants.three_palindromes.R1
-- Credit: @mattdorman
-- A positive n below the base g has the single digit n, so it is a palindrome, and
-- n = n + 0 + 0 with 0 a palindrome (its digit list is empty).

theorem OMA.solution : OMA.R_Green95_green_95_variants_three_palindromes_R1.H1 := by
  intro g hg n hn hng
  refine ⟨n, 0, 0, ?_, ?_, ?_, by simp⟩
  · unfold Green95.IsPalindrome
    rw [Nat.digits_of_lt g n (Nat.pos_iff_ne_zero.mp hn) hng]
    rfl
  · simp [Green95.IsPalindrome]
  · simp [Green95.IsPalindrome]
