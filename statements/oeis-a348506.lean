import Mathlib

/-!
# OEIS A348506: numbers k such that sigma(k) is a multiple of usigma(k)

Source: https://oeis.org/A348506
-- Credit: @jaxinator (agent: Claude Code, model claude-opus-5-5)

A348506 lists the numbers `k` such that `σ(k)` is a multiple of `usigma(k)`, where `σ` is the
sum of divisors (A000203) and `usigma(k)` is the sum of the unitary divisors of `k`, that is,
of the divisors `d` with `gcd(d, k/d) = 1` (A034448). The entry's comment: conjectured to be
the union of A005117 (the squarefree numbers) and A063880 (the numbers `k` with
`σ(k) = 2 usigma(k)`).

Conventions.
* All three sequences consist of positive integers (offset 1), so `k` ranges over `k ≥ 1`.
* `σ` is Mathlib's `ArithmeticFunction.sigma 1` and squarefree is Mathlib's `Squarefree`.
* Equality of the two sets is stated pointwise: for every `k ≥ 1`, `k` is in A348506 iff it is
  squarefree or in A063880. Right to left is easy (on squarefree `k` the two sums agree, and on
  A063880 the quotient is `2`); the content of the conjecture is left to right.
-/

namespace OMA.S_oeis_a348506

/-- The unitary sigma function (A034448): the sum of the divisors `d` of `n` with
`gcd(d, n / d) = 1`. -/
def usigma (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors.filter (fun d => Nat.Coprime d (n / d)), d

theorem main :
    ∀ k : ℕ, 0 < k →
      (usigma k ∣ ArithmeticFunction.sigma 1 k ↔
        Squarefree k ∨ ArithmeticFunction.sigma 1 k = 2 * usigma k) := by
  sorry

end OMA.S_oeis_a348506
