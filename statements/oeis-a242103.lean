import Mathlib

/-!
# A242103: m^2 - 1 as a product of three distinct Fibonacci numbers

Source: https://oeis.org/A242103 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A242103 (offset 1): numbers m such that m^2 - 1 is the product of three distinct Fibonacci numbers
> 1; data 7, 9, 11, 14, 29, 76, 121, 199, 329, 521, 659, ...
(9^2 - 1 = 80 = 2*5*8; 11^2 - 1 = 120 = 3*5*8.)

The entry records:

  Conjecture : except the numbers 9, 14, 121, 329, 659, 4523, 7307 and 212533, a(n) is a Lucas
  number (A000204).

Reading of the source:
* "three distinct Fibonacci numbers > 1": three pairwise different values `x < y < z`, each a
  Fibonacci number `Nat.fib i` and each greater than 1, with `m^2 - 1 = x * y * z`.
* The terms are positive (offset 1, first term 7); `m` ranges over the naturals with `m ≥ 1`
  (for m = 0 or 1, m^2 - 1 is not such a product anyway).
* The Lucas numbers are L(0) = 2, L(1) = 1, L(k+2) = L(k+1) + L(k); "is a Lucas number" means
  `m = L(k)` for some `k` (A000204 lists L(k) for k ≥ 1; every term is at least 7, so including
  L(0) = 2 changes nothing).
-/

namespace OMA.S_oeis_a242103

/-- The Lucas numbers: L(0) = 2, L(1) = 1, L(k+2) = L(k+1) + L(k). -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | k + 2 => lucas (k + 1) + lucas k

/-- `m` is a term of A242103: `m ≥ 1` and `m^2 - 1` is the product of three distinct Fibonacci
numbers, each greater than 1. -/
def IsTerm (m : ℕ) : Prop :=
  1 ≤ m ∧ ∃ i j k : ℕ, 1 < Nat.fib i ∧ Nat.fib i < Nat.fib j ∧ Nat.fib j < Nat.fib k ∧
    m ^ 2 - 1 = Nat.fib i * Nat.fib j * Nat.fib k

/-- Every term other than the eight listed exceptions is a Lucas number. -/
theorem main : ∀ m : ℕ, IsTerm m →
    m ∉ ({9, 14, 121, 329, 659, 4523, 7307, 212533} : Finset ℕ) → ∃ k : ℕ, m = lucas k := by
  sorry

end OMA.S_oeis_a242103
