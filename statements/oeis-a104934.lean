import Mathlib

/-!
# A104934: Expansion of (1-x)/(1 - 3*x - 2*x^2).

Source: https://oeis.org/A104934
Credit: @JeremyDevs

Formalizes the conjecture recorded in the FORMULA section of OEIS A104934 (Creighton Dement,
Apr 15 2005): Define A007483(-1) = 1. Then 2*a(n) = A007482(n) + A007483(n-1) (conjecture).

Conventions (all three sequences have offset 0 and natural-number terms):
* A104934 is the expansion of (1-x)/(1 - 3*x - 2*x^2), i.e. a(0) = 1, a(1) = 2 and
  a(n) = 3*a(n-1) + 2*a(n-2) (also stated in the entry); data 1, 2, 8, 28, 100, 356, ...
* A007482 is named in the OEIS by a combinatorial description (the number of subsequences of
  [1, ..., 2n] in which each odd number has an even neighbor). It is taken here through the
  generating function 1/(1 - 3*x - 2*x^2) and recurrence a(n) = 3*a(n-1) + 2*a(n-2) given in its
  FORMULA section, with the initial terms a(0) = 1, a(1) = 3 of its data 1, 3, 11, 39, 139, ...
  This is the function `b`.
* A007483: a(0) = 1, a(1) = 5, a(n) = 3*a(n-1) + 2*a(n-2) (its name); data 1, 5, 17, 61, 217, ...
  This is the function `c`.
* The identity is asserted for every n >= 0. For n = 0 it uses the value A007483(-1) = 1 that the
  source defines, so that case is stated separately as 2*a(0) = A007482(0) + 1; for n >= 1 the
  index n - 1 is a natural number.
-/

namespace OMA.S_oeis_a104934

/-- A104934: a(0) = 1, a(1) = 2, a(n) = 3*a(n-1) + 2*a(n-2). -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n + 2 => 3 * a (n + 1) + 2 * a n

/-- A007482: b(0) = 1, b(1) = 3, b(n) = 3*b(n-1) + 2*b(n-2). -/
def b : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | n + 2 => 3 * b (n + 1) + 2 * b n

/-- A007483: c(0) = 1, c(1) = 5, c(n) = 3*c(n-1) + 2*c(n-2). -/
def c : ℕ → ℕ
  | 0 => 1
  | 1 => 5
  | n + 2 => 3 * c (n + 1) + 2 * c n

/-- With A007483(-1) = 1: 2*a(n) = A007482(n) + A007483(n-1) for every n >= 0. -/
theorem main : 2 * a 0 = b 0 + 1 ∧ ∀ n : ℕ, 1 ≤ n → 2 * a n = b n + c (n - 1) := by
  sorry

end OMA.S_oeis_a104934
