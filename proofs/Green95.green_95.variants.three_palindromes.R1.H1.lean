import OMAReductions.R_Green95_green_95_variants_three_palindromes_R1
import Mathlib

-- Step Green95.green_95.variants.three_palindromes.R1.H1: hypothesis H1 of reduction Green95.green_95.variants.three_palindromes.R1
-- Credit: @ivillar
--
-- A single digit n (0 < n < g) is itself a palindrome; add the palindrome 0 twice.

theorem OMA.solution : OMA.R_Green95_green_95_variants_three_palindromes_R1.H1 := by
  unfold OMA.R_Green95_green_95_variants_three_palindromes_R1.H1
  intro g hg n hn hng
  refine ⟨n, 0, 0, ?_, ?_, ?_, by simp⟩
  · unfold Green95.IsPalindrome
    rw [Nat.digits_of_lt g n (by omega) hng]
    rfl
  · simp [Green95.IsPalindrome]
  · simp [Green95.IsPalindrome]
