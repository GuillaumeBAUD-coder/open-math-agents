import Mathlib

/-!
# A334996: Irregular triangle read by rows: T(n, m) is the number of ways to distribute Omega(n) objects into precisely m distinct boxes, with no box empty (Omega(n) >= m).

Source: https://oeis.org/A334996 (OEIS Foundation, CC BY-SA 4.0).
Credit: @kauanmn

The entry gives the formula (Beekman, Theorem 3 with Lemmas 1 and 2)
`T(n, m) = Sum_{k=0..m-1} (-1)^k * binomial(m, k) * tau_{m-k-1}(n)`,
where `tau_s(r) = A334997(r, s)` is computed by the entry's PARI program as
`TT(n, 0) = 1`, `TT(n, k) = Sum_{d | n} TT(d, k-1)`. This is the definition used below
(it reproduces the DATA, e.g. rows `T(12, ·) = 0, 1, 4, 3` and `T(16, ·) = 0, 1, 3, 3, 1`).
Row `n` has the entries `m = 0, ..., Omega(n)`.

The FORMULA section states:
"Conjecture: Sum_{m=0..Omega(n)} T(n, m) = A002033(n-1) for n > 1."

`A002033` (number of perfect partitions of `n`, offset 0) is defined as in its PARI program:
`a(0) = 1` and `a(n) = Sum_{d | n+1, d <= n} a(d-1)` for `n > 0`.
-/

namespace OMA.S_oeis_a334996

/-- `tau n k = A334997(n, k)` (the entry's PARI `TT`): `TT(n, 0) = 1`,
`TT(n, k) = Sum_{d | n} TT(d, k - 1)`. -/
def tau (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => ∑ d ∈ n.divisors, tau d k

/-- `T n m = Sum_{k=0..m-1} (-1)^k * binomial(m, k) * tau(n, m-k-1)`. -/
def T (n m : ℕ) : ℤ :=
  ∑ k ∈ Finset.range m, (-1) ^ k * (m.choose k : ℤ) * (tau n (m - k - 1) : ℤ)

/-- `A002033`: `a(0) = 1` and `a(n) = Sum_{d | n+1, d <= n} a(d-1)` for `n > 0`. -/
def A002033 : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ d ∈ (n + 2).properDivisors.attach, A002033 (d.1 - 1)
decreasing_by
  have h := (Nat.mem_properDivisors.mp d.2).2
  omega

/-- Sum_{m=0..Omega(n)} T(n, m) = A002033(n-1) for n > 1. -/
theorem main : ∀ n : ℕ, 1 < n →
    ∑ m ∈ Finset.range (ArithmeticFunction.cardFactors n + 1), T n m = (A002033 (n - 1) : ℤ) := by
  sorry

end OMA.S_oeis_a334996
