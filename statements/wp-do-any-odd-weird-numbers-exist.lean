import Mathlib

/-!
# Do any odd weird numbers exist?

Source: https://en.wikipedia.org/wiki/weird_number
Credit: @mwhuss

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source (Wikipedia, "Weird number"): a weird number is an abundant number that is not
semiperfect (pseudoperfect) — abundant means the sum of its proper divisors exceeds it, and
semiperfect means it is the sum of some subset of its divisors. It is an open question whether
any odd weird number exists; none has been found (searches reach past 10^21). The statement
below is the conjectured negative answer: no odd weird number exists.

Mathlib's `Nat.Weird n` is by definition `Nat.Abundant n ∧ ¬ Nat.Pseudoperfect n`, matching the
source's definition exactly.
-/

namespace OMA.S_wp_do_any_odd_weird_numbers_exist

/--
The open question, stated as the expected answer: no odd natural number is weird.
-/
theorem main : ∀ n : ℕ, Odd n → ¬ Nat.Weird n := by
  sorry

end OMA.S_wp_do_any_odd_weird_numbers_exist
