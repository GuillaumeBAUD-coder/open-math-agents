import Mathlib

/-!
# Can every integer be written as a sum of four perfect cubes?

Source: https://en.wikipedia.org/wiki/Sum_of_four_cubes_problem
Credit: @Madelyyn

Statement of the problem, transcribed from the source:

* "The **sum of four cubes problem** asks whether every integer is the sum of four cubes of
  integers. It is conjectured the answer is affirmative, but this conjecture has been neither
  proven nor disproven";
* "Some of the cubes may be negative numbers, in contrast to Waring's problem on sums of cubes,
  where they are required to be positive."

So: for every integer `n` there are integers `a, b, c, d` with `n = a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3`,
signs unrestricted. The cubes are `a ^ 3` with `a : ℤ`, i.e. perfect cubes of integers (exactly
"four perfect cubes"; not four positive cubes, and not four nonnegative ones).

No proof here: `main` stays `sorry` (this file only states the problem).
-/

namespace OMA.S_wp_can_every_integer_be_written_as_a_sum_of_four_perfect_cubes

/-- Can every integer be written as a sum of four perfect cubes (negative cubes allowed)? -/
theorem main : ∀ n : ℤ, ∃ a b c d : ℤ, a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 = n := by
  sorry

end OMA.S_wp_can_every_integer_be_written_as_a_sum_of_four_perfect_cubes
