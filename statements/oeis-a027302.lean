import Mathlib

/-!
# A027302: `a(n) = Sum_{k=0..floor((n-1)/2)} T(n,k) * T(n,k+1)`, with `T` given by A008315

Source: https://oeis.org/A027302 (OEIS Foundation, CC BY-SA 4.0).
Credit: @mbilenko03

Offset `1`, data `1, 2, 9, 24, 95, 286, 1099, 3536, 13479, 45220, 172150, ...`.

A008315 is the Catalan triangle (ballot numbers): its row `m` is `C(m,k) - C(m,k-1)`,
`0 ≤ k ≤ floor(m/2)` (rows `1`, `1`, `1 1`, `1 2`, `1 3 2`, `1 4 5`, `1 5 9 5`, ...).

Reading of the indices. Taken literally with the row index `n` of A008315, the sum gives
`a(1) = T(1,0) * T(1,1)`, where `T(1,1)` is not an entry of the triangle (row `1` is just `1`), and
the formula `C(1,1) - C(1,0) = 0` would give `a(1) = 0`, not the listed `1`. The data is reproduced
exactly when row `n` of the sum is row `n + 1` of A008315 (the triangle rows counted from `1`):
`a(n) = Sum_{k=0..floor((n-1)/2)} T(n+1,k) * T(n+1,k+1)`. For example
`a(1) = 1 * 1 = 1`, `a(2) = 1 * 2 = 2`, `a(3) = 1 * 3 + 3 * 2 = 9`, `a(4) = 1 * 4 + 4 * 5 = 24`.
With this reading every factor `T(n+1, k+1)`, `k+1 ≤ floor((n+1)/2)`, is an entry of the triangle.
We formalize this reading (checked against the first 26 data terms).

Conjecture (R. J. Mathar, Nov 22 2024): D-finite with recurrence
`-(n+2)*(13*n-2)*(3+n)^2*a(n) +10*(8*n^2+3*n-8)*(n+2)^2*a(n-1)
 +8*(12*n^4+47*n^3+52*n^2+67*n+20)*a(n-2) -160*(8*n^2+3*n-8)*(n-1)^2*a(n-3)
 +128*(7*n+4)*(2*n-5)*(-2+n)^2*a(n-4) = 0`,
stated for `n ≥ 5`, the indices where `a(n-4)` is a term (offset `1`).
-/

namespace OMA.S_oeis_a027302

/-- A008315: the ballot number `T(m,k) = C(m,k) - C(m,k-1)` (with `C(m,-1) = 0`). -/
def T (m : ℕ) : ℕ → ℤ
  | 0 => 1
  | k + 1 => (m.choose (k + 1) : ℤ) - (m.choose k : ℤ)

/-- A027302, offset `1`: `a(n) = ∑_{k=0..floor((n-1)/2)} T(n+1,k) * T(n+1,k+1)`. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range ((n - 1) / 2 + 1), T (n + 1) k * T (n + 1) (k + 1)

/-- Conjecture (R. J. Mathar): the order-4 recurrence of A027302, for `n ≥ 5`. -/
theorem main :
    ∀ n : ℕ, 5 ≤ n →
      -((n : ℤ) + 2) * (13 * n - 2) * (3 + n) ^ 2 * a n
        + 10 * (8 * (n : ℤ) ^ 2 + 3 * n - 8) * (n + 2) ^ 2 * a (n - 1)
        + 8 * (12 * (n : ℤ) ^ 4 + 47 * n ^ 3 + 52 * n ^ 2 + 67 * n + 20) * a (n - 2)
        - 160 * (8 * (n : ℤ) ^ 2 + 3 * n - 8) * (n - 1) ^ 2 * a (n - 3)
        + 128 * (7 * (n : ℤ) + 4) * (2 * n - 5) * (-2 + n) ^ 2 * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a027302
