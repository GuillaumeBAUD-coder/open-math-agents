import Mathlib

/-!
# A038396: Concatenate first n even numbers in reverse order.

Source: https://oeis.org/A038396
Credit: @eitanteperman

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a038396

/-- A038396: concatenate the first n even numbers in reverse order: a(n) = "2n (2n-2) ... 4 2" in
decimal (offset 1; a(1) = 2, a(2) = 42, a(3) = 642, ...). Prepending `2n` to the decimal string of
`a (n-1)` is `2n * 10 ^ (number of digits of a (n-1)) + a (n-1)`. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * (n + 1) * 10 ^ (Nat.digits 10 (a n)).length + a n

/-- `m` is a perfect power: `m = b ^ k` with `k ≥ 2`. -/
def IsPerfectPower' (m : ℕ) : Prop := ∃ b k : ℕ, 2 ≤ k ∧ m = b ^ k

/-- Smarandache's conjecture (A038396): a(n) is never a perfect power, for every n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ¬ IsPerfectPower' (a n) := by
  sorry

end OMA.S_oeis_a038396
