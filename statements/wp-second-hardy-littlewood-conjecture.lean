import Mathlib

/-!
# Second Hardy–Littlewood conjecture

Source: https://en.wikipedia.org/wiki/Second_Hardy–Littlewood_conjecture
Credit: @mwhuss

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source (Hardy–Littlewood 1923): π(x + y) ≤ π(x) + π(y) for integers x, y ≥ 2, where π(z)
is the prime-counting function (the number of primes up to and including z).
Mathlib's `Nat.primeCounting n` counts the primes ≤ n, matching the source.
-/

namespace OMA.S_wp_second_hardy_littlewood_conjecture

/--
The second Hardy–Littlewood conjecture: for integers x, y ≥ 2,
π(x + y) ≤ π(x) + π(y).
-/
theorem main :
    ∀ x y : ℕ, 2 ≤ x → 2 ≤ y →
      Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y := by
  sorry

end OMA.S_wp_second_hardy_littlewood_conjecture
