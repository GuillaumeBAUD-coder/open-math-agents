import Mathlib

/-!
# OEIS A370574: n^2 XOR k^2 a positive square

Source: https://oeis.org/A370574 (OEIS Foundation, CC BY-SA 4.0).

Entry: a(n) is the least k > 0 such that n^2 XOR k^2 is a positive square
number (where XOR denotes the bitwise XOR operator), or -1 if no such k exists
(offset 1; a(1) = a(2) = -1).

Conjecture (Rémy Sigrist, Feb 22 2024): a(n) > 0 for any n > 2.

Formalization notes:
* Bitwise XOR on natural numbers is `Nat.xor`, written `^^^`.
* a(n) > 0 means some k > 0 has n^2 XOR k^2 = m^2 with m > 0.
-/

namespace OMA.S_oeis_a370574

/-- For every n > 2 there is k > 0 such that n^2 XOR k^2 is a positive square. -/
theorem main : ∀ n : ℕ, 2 < n → ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ n ^ 2 ^^^ k ^ 2 = m ^ 2 := by
  sorry

end OMA.S_oeis_a370574
