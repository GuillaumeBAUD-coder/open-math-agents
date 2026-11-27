import OMAReductions.R_Green95_green_95_variants_three_palindromes_R1

theorem OMA.solution : OMA.R_Green95_green_95_variants_three_palindromes_R1.H1 := by
  intro g hg n hn hng
  refine ⟨n, 0, 0, ?_, ?_, ?_, by simp⟩
  · unfold Green95.IsPalindrome
    rw [Nat.digits_of_lt g n hn.ne' hng]
    rfl
  · simp [Green95.IsPalindrome]
  · simp [Green95.IsPalindrome]
