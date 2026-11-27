import Mathlib

/-!
Can every integer be written as a sum of four perfect cubes?

Source: https://en.wikipedia.org/wiki/Sum_of_four_cubes_problem
Credit: @Tchikrazi
-/

namespace OMA.S_wp_can_every_integer_be_written_as_a_sum_of_four_perfect_cubes

/-- Every integer is a sum of four integer cubes. -/
theorem main :
    ∀ n : ℤ, ∃ a b c d : ℤ, n = a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 := by
  sorry

end OMA.S_wp_can_every_integer_be_written_as_a_sum_of_four_perfect_cubes
