import Mathlib

/-!
# A394815: Numbers k in A014574 (averages of twin prime pairs) such that gcd(k, sigma(k)) = 2.

Source: https://oeis.org/A394815
Credit: @azmiozgen

Conjecture (from the entry): every term is divisible by 36.

Formalization notes:
* A014574: the numbers k with k - 1 and k + 1 both prime.
* Stated as: for every k with k - 1 and k + 1 prime and gcd(k, sigma(k)) = 2, 36 divides k.
* Controls (computed): the terms below 150000 are 5652, 6948, 16452, 20772, 27792, 44532, 65700,
  67428, 126612, 143568, as in the entry; every term below 300000 is divisible by 36.
-/

namespace OMA.S_oeis_a394815

open ArithmeticFunction

/-- Every twin-prime average `k` with `gcd(k, σ(k)) = 2` is divisible by 36. -/
theorem main :
    ∀ k : ℕ, (k - 1).Prime → (k + 1).Prime → Nat.gcd k (sigma 1 k) = 2 → 36 ∣ k := by
  sorry

end OMA.S_oeis_a394815
