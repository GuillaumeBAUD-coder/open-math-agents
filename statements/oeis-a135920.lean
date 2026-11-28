import Mathlib

/-!
# A135920: O.g.f.: A(x) = Sum_{n>=0} x^n / Product_{k=0..n} (1 - k^2*x).

Source: https://oeis.org/A135920
Credit: @thatoneguy006

The conjecture stated here, from the entry:

  Conjecture: a(n) = A369527(n-1, 0) = A369595(n-1, 0) for n > 0 with a(0) = 1.
  - Mikhail Kurkov, Apr 25 2024

Definitions.
* A135920 (offset 0). The coefficient of x^n in x^k / Product_{j=0..k} (1 - j^2*x) is
  S(n, k) with S(0, 0) = 1, S(n, 0) = 0 for n > 0, S(0, k) = 0 for k > 0 and
  S(n, k) = S(n-1, k-1) + k^2*S(n-1, k) (the central factorial triangle A036969, whose row sums
  the entry identifies with this sequence); summing over k gives
  a(n) = Sum_{k=0..n} S(n, k), the definition used here. It reproduces the data
  1, 1, 2, 7, 37, 264, 2433, 27913, ...
* A369527 (array, n, k >= 0): A(0,k) = 1 and A(n,k) = (k+1)^2*A(n-1,k) + A(n-1,k+1).
  Rows: 1, 1, 1, ...; 2, 5, 10, 17, ...; 7, 30, 107, 298, ...
* A369595 (array, n, k >= 0): A(0,k) = 1 and A(n,k) = A(n-1,k+2) + Sum_{j=0..k} C(k,j)*A(n-1,j).
  Rows: 1, 1, 1, ...; 2, 3, 5, 9, ...; 7, 14, 30, 68, ...
-/

namespace OMA.S_oeis_a135920

/-- `S n k`: the coefficient of `x^n` in `x^k / ∏_{j=0..k} (1 - j^2 x)`. -/
def S : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => S n k + (k + 1) ^ 2 * S n (k + 1)

/-- A135920: the coefficient of `x^n` in `Sum_{m>=0} x^m / ∏_{k=0..m} (1 - k^2 x)`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), S n k

/-- The array A369527. -/
def A369527 : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, k => (k + 1) ^ 2 * A369527 n k + A369527 n (k + 1)

/-- The array A369595. -/
def A369595 : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, k => A369595 n (k + 2) + ∑ j ∈ Finset.range (k + 1), k.choose j * A369595 n j

/-- Kurkov's conjecture: `a(n) = A369527(n-1, 0) = A369595(n-1, 0)` for `n > 0`. -/
theorem main : ∀ n : ℕ, 0 < n → a n = A369527 (n - 1) 0 ∧ a n = A369595 (n - 1) 0 := by
  sorry

end OMA.S_oeis_a135920
