import Mathlib

/-!
# Can every integer be written as a sum of four perfect cubes?

Source: https://en.wikipedia.org/wiki/Sum_of_four_cubes_problem
Credit: @John-A-McMahon

Source statement (Wikipedia, *Sum of four cubes problem*): the problem asks whether every
integer is the sum of four cubes of integers. Cubes of negative integers are allowed (in
contrast to Waring's problem), and every integer, negative ones included, is meant. It is
conjectured that the answer is affirmative; stated here in that positive form. (Known: all
integers not congruent to 4 or 5 modulo 9 are such sums, by explicit identities.)
-/

namespace OMA.S_wp_can_every_integer_be_written_as_a_sum_of_four_perfect_cubes

theorem main : ∀ n : ℤ, ∃ a b c d : ℤ, n = a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 := by
  sorry

end OMA.S_wp_can_every_integer_be_written_as_a_sum_of_four_perfect_cubes
