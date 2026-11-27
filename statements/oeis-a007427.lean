import Mathlib

/-!
# A007427: Moebius transform applied twice to sequence 1,0,0,0,....

Source: https://oeis.org/A007427
Credit: @maaaakks

Conjecture (Ralf Stephan, Jul 05 2013), from the OEIS entry:

> Dirichlet g.f. of |a(n)|: zeta(s)^2/zeta(2s)^2 (conjectured).

(The entry later notes that the conjecture is correct because
`1 + Sum_{e>=1} binomial(2,e)/p^(e*s) = (p^s+1)^2/p^(2s)`, whose product over `p`
is `zeta(s)^2/zeta(2s)^2`.)

## Definitions

* `a = μ * μ` is the Moebius transform applied twice to `1,0,0,0,...` (the Dirichlet
  identity `δ`), i.e. the Dirichlet convolution of the Moebius function with itself:
  `a(n) = Σ_{d ∣ n} μ(d) μ(n/d)`, offset 1. In Mathlib this is
  `ArithmeticFunction.moebius * ArithmeticFunction.moebius` (`*` is Dirichlet convolution),
  as an `ArithmeticFunction ℤ`; its value at `0` is `0` by convention and plays no role.
* The Dirichlet generating function of `|a(n)|` is the L-series
  `LSeries (fun n ↦ (|a n| : ℂ)) s = Σ_{n ≥ 1} |a(n)| / n^s` (Mathlib's `LSeries` ignores the
  `n = 0` term).

## Domain of `s`

A Dirichlet generating function is an identity of functions only where the series converges.
Since `0 ≤ |a(n)| ≤ d(n)` (number of divisors) and `|a(n)| = 1` for `n` a perfect square of a
squarefree number, the series `Σ |a(n)| n^{-s}` converges absolutely exactly for `Re s > 1`
(it diverges at `s = 1`, as `|a(n)| ≥ |μ(n)|`). On this half-plane `riemannZeta (2 * s) ≠ 0`,
so the right-hand side is a genuine value. We therefore state the identity for every complex
`s` with `1 < s.re`.
-/

namespace OMA.S_oeis_a007427

open ArithmeticFunction

/-- `a(n) = Σ_{d ∣ n} μ(d) μ(n/d)`: the Moebius transform applied twice to `1,0,0,0,...`. -/
def a : ArithmeticFunction ℤ := moebius * moebius

theorem main : ∀ s : ℂ, 1 < s.re →
    LSeries (fun n ↦ ((|a n| : ℤ) : ℂ)) s = riemannZeta s ^ 2 / riemannZeta (2 * s) ^ 2 := by
  sorry

end OMA.S_oeis_a007427
