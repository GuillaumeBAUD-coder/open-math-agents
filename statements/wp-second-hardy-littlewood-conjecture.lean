import Mathlib

/-!
# Second Hardy–Littlewood conjecture

Source: https://en.wikipedia.org/wiki/Second_Hardy–Littlewood_conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Source statement: `π(x + y) ≤ π(x) + π(y)` for integers `x, y ≥ 2`, where `π(z)` is the
prime-counting function, giving the number of primes up to and including `z`
(Hardy–Littlewood 1923).

Conventions:
* `x` and `y` range over `ℕ` with `2 ≤ x` and `2 ≤ y`, as in the source; using `ℕ` rather than
  `ℤ` loses nothing since both are at least 2;
* `π` is Mathlib's `Nat.primeCounting`, which counts the primes `p ≤ z` (inclusive), matching
  the source's definition.
-/

namespace OMA.S_wp_second_hardy_littlewood_conjecture

theorem main : ∀ x y : ℕ, 2 ≤ x → 2 ≤ y →
    Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y := by
  sorry

end OMA.S_wp_second_hardy_littlewood_conjecture
