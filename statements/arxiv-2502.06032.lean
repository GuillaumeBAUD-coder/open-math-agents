import Mathlib

/-!
# Positivity of quotients of $q$-binomial coefficients with the same top argument

Source: M. Gatzweiler and C. Krattenthaler, *A positivity conjecture for a quotient of
$q$-binomial coefficients*, https://arxiv.org/abs/2502.06032 (Conjecture 1)
Credit: @SulkBash

## The problem (as the source states it)

With $[n]_q = \frac{1-q^n}{1-q}$, $[n]_q! = [n]_q [n-1]_q \cdots [1]_q$ and
$\left[{n \atop k}\right]_q = \frac{[n]_q!}{[k]_q!\,[n-k]_q!}$ for $0 \le k \le n$ (and $0$
otherwise):

**Conjecture 1.** Let $n, k, l$ be non-negative integers. If
$$\frac{\left[{n \atop k}\right]_q}{\left[{n \atop l}\right]_q}
  = \frac{[l]_q!\,[n-l]_q!}{[k]_q!\,[n-k]_q!}$$
is a polynomial (in $q$), then it has non-negative coefficients.

The paper proves the cases $l = k - 3$ and $l = 2$, recalls the known cases $l = k, k - 1,
k - 2, 0, 1$, and reports a computer verification for all $n \le 400$.

## Formalization notes

* **Definition.** `qBinom n k : ℚ[X]` is $\left[{n \atop k}\right]_q$, defined by the q-Pascal
  rule $\left[{n+1 \atop k+1}\right]_q = \left[{n \atop k}\right]_q
  + q^{k+1}\left[{n \atop k+1}\right]_q$. Its boundary values are
  $\left[{n \atop 0}\right]_q = 1$ and $\left[{0 \atop k+1}\right]_q = 0$.
  - This is a standard identity for the source's factorial formula, and it gives the value `0`
    for `k > n`, as in the source.
* **Range.** The quotient in (1) is formed for `k, l ≤ n`, the range in which the q-factorial
  expression is defined. There `qBinom n l ≠ 0`.
* **Statement.** "The quotient is a polynomial" is read as: there is `P : ℚ[X]` with
  `qBinom n l * P = qBinom n k`. The conclusion is `0 ≤ P.coeff i` for every `i`.
  - Rational coefficients are the most general reading. Since `qBinom n l` is monic with integer
    coefficients, any such `P` has integer coefficients anyway.
-/

namespace OMA.S_arxiv_2502_06032

open Polynomial

/-- The `q`-binomial coefficient `[n, k]_q`, via the `q`-Pascal rule. -/
noncomputable def qBinom : ℕ → ℕ → ℚ[X]
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qBinom n k + X ^ (k + 1) * qBinom n (k + 1)

/-- Gatzweiler–Krattenthaler Conjecture 1: whenever `[n, k]_q / [n, l]_q` is a polynomial, all its
coefficients are non-negative. -/
theorem main :
    ∀ n k l : ℕ, k ≤ n → l ≤ n →
      ∀ P : ℚ[X], qBinom n l * P = qBinom n k → ∀ i : ℕ, 0 ≤ P.coeff i := by
  sorry

end OMA.S_arxiv_2502_06032
