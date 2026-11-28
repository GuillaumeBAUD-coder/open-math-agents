import Mathlib

/-!
# A233390: a(n) = |{0 < k < n: 2^k - 1 + q(n-k) is prime}|, where q(.) is the strict partition function (A000009).

Source: https://oeis.org/A233390
Credit: @gblacher2

Conjecture (Zhi-Wei Sun, comment in A233390): "a(n) > 0 for all n > 1." That is, for every
`n > 1` there is some `k` with `0 < k < n` such that `2^k - 1 + q(n - k)` is prime.

Conventions:
* `q(m)` is the number of partitions of `m` into distinct parts (A000009), the cardinality of
  Mathlib's finset `Nat.Partition.distincts m` (1, 1, 1, 2, 2, 3, 4, 5, … for `m = 0, 1, 2, …`).
* For `k > 0`, `2^k - 1 ≥ 1`, so the natural-number subtraction is the true value.

With these definitions `a(1), …, a(10)` are 0, 1, 1, 1, 2, 1, 2, 2, 2, 1, as in the OEIS data
(for example `a(6) = 1` from `2^2 - 1 + q(4) = 5`), and the first 1500 terms of the b-file are
reproduced.
-/

namespace OMA.S_oeis_a233390

/-- The strict partition function A000009: the number of partitions of `m` into distinct
parts. -/
def q (m : ℕ) : ℕ := (Nat.Partition.distincts m).card

/-- A233390: `a n` is the number of `k` with `0 < k < n` such that `2^k - 1 + q (n - k)` is
prime. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 n).filter (fun k => (2 ^ k - 1 + q (n - k)).Prime)).card

/-- Sun's conjecture: `a(n) > 0` for all `n > 1`. -/
theorem main : ∀ n : ℕ, 1 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a233390
