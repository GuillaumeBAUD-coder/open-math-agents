import Mathlib

/-!
# A000720: pi(n), the number of primes <= n. Sometimes called PrimePi(n) to distinguish it from the number 3.14159...

Source: https://oeis.org/A000720
Credit: @mattdorman

The source states: the second Hardy–Littlewood conjecture, that `π(x) + π(y) ≥ π(x + y)` for
integers `x` and `y` with `min{x, y} ≥ 2`.

Reading used here: `x, y` are natural numbers (`π` of a negative number is not meant) with
`x ≥ 2` and `y ≥ 2`, and `π = Nat.primeCounting`, the number of primes `≤ n`. The source adds a
remark about large `(x, y)`; the conjecture itself is the inequality for all such `x, y`. (It is
widely believed to be false, being incompatible with the prime `k`-tuples conjecture; a
disproof settles it equally.)
-/

namespace OMA.S_oeis_a000720

theorem main :
    ∀ x y : ℕ, 2 ≤ x → 2 ≤ y →
      Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y := by
  sorry

end OMA.S_oeis_a000720
