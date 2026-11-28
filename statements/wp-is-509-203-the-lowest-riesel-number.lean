import Mathlib

/-!
# Is 509,203 the lowest Riesel number?

Source: https://en.wikipedia.org/wiki/Riesel_number
Credit: @mwhuss

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: a Riesel number is an odd natural number k for which k·2^n − 1 is composite for all
natural numbers n. Riesel (1956) showed 509203 has this property ("not prime for any integer n").
The Riesel problem asks for the smallest Riesel number; since no covering set has been found for
any k < 509203, it is conjectured to be the smallest.
-/

namespace OMA.S_wp_is_509_203_the_lowest_riesel_number

/-- k is a Riesel number: odd, and k·2^n − 1 is composite (not prime) for every n. -/
def IsRiesel (k : ℕ) : Prop := Odd k ∧ ∀ n : ℕ, ¬ Nat.Prime (k * 2 ^ n - 1)

/--
The Riesel problem's conjectured answer: 509,203 is a Riesel number and no smaller k is.
-/
theorem main : IsRiesel 509203 ∧ ∀ k : ℕ, k < 509203 → ¬ IsRiesel k := by
  sorry

end OMA.S_wp_is_509_203_the_lowest_riesel_number
