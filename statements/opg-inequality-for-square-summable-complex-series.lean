import Mathlib

/-!
Retkes's inequality for square-summable complex series.
Source: https://www.openproblemgarden.org/op/inequality_for_square_summable_complex_series
Credit: @con123-gif
The source indexes the input sequence from one. The unused value a 0
is arbitrary. Both nonnegative outer sums are real, and the inner sum
is complex. A proof was published in the source's comments in 2013.
-/

namespace OMA.S_opg_inequality_for_square_summable_complex_series

theorem main (a : ℕ → ℂ)
    (ha : Summable (fun n : ℕ => ‖a (n + 1)‖ ^ 2)) :
    (∑' n : ℕ, ‖a (n + 1)‖ ^ 2) ≥
      (6 / Real.pi ^ 2) *
        (∑' k : ℕ, ‖∑' l : ℕ, a (2 ^ k * (2 * l + 1)) / ((l : ℂ) + 1)‖ ^ 2) := by
  sorry

end OMA.S_opg_inequality_for_square_summable_complex_series
