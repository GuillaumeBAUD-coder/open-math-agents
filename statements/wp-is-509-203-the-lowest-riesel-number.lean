import Mathlib

/-!
# Is 509,203 the lowest Riesel number?

Source: https://en.wikipedia.org/wiki/Riesel_number
Credit: @Andyi955

A Riesel number is an odd natural number `k` for which `k * 2 ^ n - 1` is composite for all natural
numbers `n`. The number `509203` is known to be a Riesel number (a covering system shows every
`509203 * 2 ^ n - 1` has a small prime divisor), and it is conjectured to be the smallest one: for
every odd `k < 509203` some `k * 2 ^ n - 1` is prime (Wikipedia, Riesel number). The question asked,
whether `509203` is the lowest Riesel number, is exactly `main` below.

## Encoding

* `IsRieselNumber k` is the source's definition: `k` is odd and `k * 2 ^ n - 1` is composite for
  every `n`. Compositeness is written as `1 < k * 2 ^ n - 1` together with `Not Prime` (Mathlib has
  no separate compositeness predicate), which is the same thing for these numbers.
* The conjecture is stated in full: `509203` is a Riesel number and no smaller odd `k` is, the
  latter written as `∃ n, (k * 2 ^ n - 1).Prime` for every odd `k < 509203`.
-/

namespace OMA.S_wp_is_509_203_the_lowest_riesel_number

/-- `IsRieselNumber k` holds when `k` is odd and `k * 2 ^ n - 1` is composite for every `n`. -/
def IsRieselNumber (k : ℕ) : Prop :=
  Odd k ∧ ∀ n : ℕ, 1 < k * 2 ^ n - 1 ∧ ¬ (k * 2 ^ n - 1).Prime

/-- **Is 509,203 the lowest Riesel number?**: `509203` is a Riesel number and every odd
`k < 509203` has some `n` with `k * 2 ^ n - 1` prime. -/
theorem main : IsRieselNumber 509203 ∧
    ∀ k : ℕ, Odd k → 0 < k → k < 509203 → ∃ n : ℕ, (k * 2 ^ n - 1).Prime := by
  sorry

end OMA.S_wp_is_509_203_the_lowest_riesel_number
