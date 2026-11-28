import Mathlib

/-!
# A154404: Number of ways to express n as the sum of an odd prime, a positive Fibonacci number and a Catalan number.

Source: https://oeis.org/A154404
Credit: @gblacher2

Conjecture (Qing-Hu Hou and Jiang Zeng, Jan 09 2009, comment in A154404): "a(n) > 0 for every
n = 5, 6, ...". In Z.-W. Sun, "Mixed sums of primes and other terms" (arXiv:0901.3075),
Conjecture 1.13 (Hou and Zeng) reads: any integer `n > 4` can be written as the sum of an odd
prime, a positive Fibonacci number and a Catalan number.

Conventions (as in the OEIS formula `a(n) = |{<p,s,t>: p + F_s + C_t = n, p an odd prime, s > 1}|`
and its PARI program):
* `F s` is Mathlib's `Nat.fib s` (`F 0 = 0`, `F 1 = 1`); the positive Fibonacci numbers are
  `F s` with `s ≥ 1`, and the index `s ≥ 2` lists each of them once (1, 2, 3, 5, 8, …).
* `C t` is Mathlib's `catalan t = (2t choose t) / (t + 1)` (1, 1, 2, 5, 14, …); the index
  `t ≥ 1` lists each Catalan number once (1, 2, 5, 14, …).
* `a n` counts the triples `(p, s, t)` with `p` an odd prime, `s ≥ 2`, `t ≥ 1` and
  `p + F s + C t = n`. All three entries are bounded as in the finsets below, because
  `F s ≥ s - 1` and `C t ≥ t` for `t ≥ 1`.

With these definitions `a(1), …, a(12)` are 0, 0, 0, 0, 1, 2, 3, 3, 5, 5, 5, 4, as in the OEIS
data (for example `a(7) = 3` from `3 + 2 + 2`, `3 + 3 + 1`, `5 + 1 + 1`), and the 100000 terms of
the b-file are reproduced.
-/

namespace OMA.S_oeis_a154404

/-- A154404: the number of triples `(p, s, t)` with `p` an odd prime, `s ≥ 2`, `t ≥ 1` and
`p + F s + C t = n`, where `F` is the Fibonacci sequence and `C` the Catalan numbers. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ (Finset.Icc 2 (n + 1) ×ˢ Finset.Icc 1 n)).filter
    (fun x : ℕ × ℕ × ℕ =>
      x.1.Prime ∧ Odd x.1 ∧ x.1 + Nat.fib x.2.1 + catalan x.2.2 = n)).card

/-- The Hou–Zeng conjecture: `a(n) > 0` for every `n ≥ 5`. -/
theorem main : ∀ n : ℕ, 4 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a154404
