import Mathlib

/-!
# OEIS A356492: determinants of prime Toeplitz matrices

Source: https://oeis.org/A356492
Credit: @SudharsanAnimations

`A356492(n)` is the determinant of the symmetric Toeplitz matrix `M(n)` whose first row is
`prime(n), prime(n-1), …, prime(1)`. Robert Israel conjectured that `a(n)` is prime only for
`n = 1` and `n = 2`; the entry records the reason: for `n ≥ 4`, all rows except the first and the
last consist of odd numbers, which makes `a(n)` even. We state this proved result for all `n ≥ 0`
(offset `0`, `a(0) = 1`): `a(n)` is prime iff `n = 1` or `n = 2`.

Conventions: `prime(k)` is `Nat.nth Nat.Prime (k - 1)` (so `prime(1) = 2`); `M(n)_{i,j} =
prime(n - |i - j|)` for `0 ≤ i, j < n`; the determinant is over `ℤ`, and "prime" is `Prime` in `ℤ`
(so a negative determinant is prime iff its absolute value is).
-/

namespace OMA.S_oeis_a356492

/-- `M(n)`: the symmetric Toeplitz matrix whose first row is `prime(n), prime(n-1), …, prime(1)`,
i.e. `M(n)_{i,j} = prime(n - |i - j|)` (1-based primes; `Nat.nth Nat.Prime 0 = 2`). -/
noncomputable def M (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => (Nat.nth Nat.Prime (n - 1 - Nat.dist i j) : ℤ)

/-- `A356492(n) = det M(n)`. -/
noncomputable def a (n : ℕ) : ℤ := (M n).det

theorem main : ∀ n : ℕ, (Prime (a n) ↔ n = 1 ∨ n = 2) := by
  sorry

end OMA.S_oeis_a356492
