import Mathlib

/-!
# A209802: partial sums of the exponential Möbius function are positive

Source: https://oeis.org/A209802 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A209802 (offset 1): partial sums of the exponential Möbius function A166234; data
1, 2, 3, 2, 3, 4, 5, 4, 3, 4, ...

The entry records:

  Analog of Mertens's function, A002321; conjecture: a(n) > 0.

Reading of the source:
* The exponential Möbius function (A166234) is multiplicative with value μ(e) at a prime power
  p^e (e ≥ 1), where μ is the Möbius function: for `n = ∏ p^(e_p)`,
  `μ^(e)(n) = ∏_p μ(e_p)`, and `μ^(e)(1) = 1`. In Lean this is the product over the
  factorization of `n` of `μ` applied to the exponents.
* `a n = ∑_{k=1}^{n} μ^(e)(k)`, an integer.
* The conjecture: `a(n) > 0` for every `n ≥ 1`.
-/

namespace OMA.S_oeis_a209802

open ArithmeticFunction

/-- The exponential Möbius function: `∏_{p^e ∥ n} μ(e)` (equal to 1 at `n = 1`). -/
def expMoebius (n : ℕ) : ℤ := n.factorization.prod fun _ e => moebius e

/-- A209802(n) = ∑_{k=1}^{n} μ^(e)(k). -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, expMoebius k

/-- The conjecture: every partial sum is positive. -/
theorem main : ∀ n : ℕ, 1 ≤ n → 0 < a n := by
  sorry

end OMA.S_oeis_a209802
