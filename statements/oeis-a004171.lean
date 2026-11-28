import Mathlib

/-!
# A004171: a(n) = 2^(2n+1).

Source: https://oeis.org/A004171
Credit: @tczyzycki

Formalizes Alonso del Arte's comment on OEIS A004171 (Oct 01 2019):
a number of the form `2 ^ (2 * n + 1)` can never be the first power of 2 in a
Collatz sequence, except for the Collatz sequence starting with that number.
-/

namespace OMA.S_oeis_a004171

/-- One step of the Collatz map on natural numbers. -/
def collatzStep (m : ℕ) : ℕ :=
  if m % 2 = 0 then m / 2 else 3 * m + 1

/-- Predicate stating that a natural number is a power of 2 (`2 ^ e` for some `e : ℕ`). -/
def IsPowerOfTwo (m : ℕ) : Prop :=
  ∃ e : ℕ, m = 2 ^ e

theorem main :
    ∀ n m k : ℕ, 0 < m → m ≠ 2 ^ (2 * n + 1) →
      collatzStep^[k] m = 2 ^ (2 * n + 1) →
      ∃ j < k, IsPowerOfTwo (collatzStep^[j] m) := by
  sorry

end OMA.S_oeis_a004171
