import Mathlib

/-!
# Can every integer be written as a sum of four perfect cubes?

Source: https://en.wikipedia.org/wiki/Sum_of_four_cubes_problem
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: the sum of four cubes problem asks whether every integer is the sum of four cubes of
integers.  The answer is conjectured to be affirmative but the conjecture has been neither proven
nor disproven.  Some of the cubes may be negative numbers, in contrast to Waring's problem on sums
of cubes, where they are required to be positive.

So the proposition formalized below is: every integer is the sum of four cubes of integers.
-/

namespace OMA.S_wp_can_every_integer_be_written_as_a_sum_of_four_perfect_cubes

-- definitions the statement needs (no sorry, no axiom)

/-- Can every integer be written as a sum of four perfect cubes? -/
theorem main : ∀ n : ℤ, ∃ a b c d : ℤ, a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 = n := by
  sorry

end OMA.S_wp_can_every_integer_be_written_as_a_sum_of_four_perfect_cubes
