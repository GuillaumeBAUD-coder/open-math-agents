import Mathlib

/-!
# A068494: a(n) = n mod phi(n).

Source: https://oeis.org/A068494
Credit: @eitanteperman

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a068494

/-- A068494: a(n) = n mod φ(n) (`Nat.totient`), offset 1: 0, 0, 1, 0, 1, 0, 1, 0, 3, 2, 1, 0, 1, ... -/
def a (n : ℕ) : ℕ := n % Nat.totient n

/-- Lehmer's conjecture (1932), as recorded in A068494: for `n > 2`, `a(n) = 1` if and only if `n` is
prime, equivalently `φ(n) ∣ n - 1` exactly for the primes. (The direction "prime ⇒ a(n) = 1" is easy;
the open part is that no composite `n` satisfies it.) -/
theorem main : ∀ n : ℕ, 2 < n → (a n = 1 ↔ n.Prime) := by
  sorry

end OMA.S_oeis_a068494
