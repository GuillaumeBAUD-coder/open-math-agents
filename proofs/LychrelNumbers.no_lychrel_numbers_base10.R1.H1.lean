import OMAReductions.R_LychrelNumbers_no_lychrel_numbers_base10_R1

-- Step LychrelNumbers.no_lychrel_numbers_base10.R1.H1
-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: one Lychrel step sends 56 to 56 + 65 = 121, a palindrome; checked by decide.

theorem OMA.solution : OMA.R_LychrelNumbers_no_lychrel_numbers_base10_R1.H1 := by
  refine ⟨1, ?_⟩
  dsimp [LychrelNumbers.IsPalindrome10]
  decide
