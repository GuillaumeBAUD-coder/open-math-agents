import Mathlib

/-!
# A102396: A mod 2 related Jacobsthal sequence.

Source: https://oeis.org/A102396
Credit: @ShoQo

Conjecture: "all the terms are Jacobsthal numbers." (Paul Barry, Jan 07 2005: "The conjecture is
true since a(n) = A001045(A000120(n)).")

Formalization notes:
* Offset 0, a(n) = Sum_{k=0..n} [n+k ≡ 1 (mod 3)] (C(n,k) mod 2), the entry's formula
  (data: 0, 1, 1, 1, 1, 1, 1, 3, ...).
* Jacobsthal numbers A001045: J(0) = 0, J(1) = 1, J(n+2) = J(n+1) + 2 J(n).
-/

namespace OMA.S_oeis_a102396

/-- a(n) = Σ_{k ≤ n, n+k ≡ 1 (mod 3)} (C(n,k) mod 2). -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if (n + k) % 3 = 1 then n.choose k % 2 else 0

/-- The Jacobsthal numbers A001045. -/
def jacobsthal : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => jacobsthal (n + 1) + 2 * jacobsthal n

theorem main : ∀ n : ℕ, ∃ m : ℕ, a n = jacobsthal m := by
  sorry

end OMA.S_oeis_a102396
