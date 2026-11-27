import Mathlib

/-!
# Erdős Problem 411

Source: https://www.erdosproblems.com/411
Credit: @hermitokatt

## The problem

Let $g_1 = g(n) = n + \phi(n)$ and $g_k(n) = g(g_{k-1}(n))$. For which $n$ and $r$ is it true
that $g_{k+r}(n) = 2 g_k(n)$ for all large $k$?

The known solutions to $g_{k+2}(n) = 2 g_k(n)$ are $n = 10$ and $n = 94$. Selfridge and
Weintraub found solutions to $g_{k+9}(n) = 9 g_k(n)$, and Weintraub found
$g_{k+25}(3114) = 729 g_k(3114)$ for all $k \ge 6$. Steinerberger [St25] observed that for
$r = 2$ the problem is equivalent to $\phi(n) + \phi(n + \phi(n)) = n$. Cambie conjectures that
the only solutions have $r = 2$ and $n = 2^l p$ for some $l \ge 1$ and
$p \in \{2, 3, 5, 7, 35, 47\}$.

## Formalization notes

* The question is "for which $n$ and $r$". The source gives a conjectured answer (Cambie's), and
  this file states that answer.
* `g n = n + φ n`, and `g^[k] n` is $g_k(n)$, with `g^[0] n = n`. The condition only concerns
  large `k`, so the value at `k = 0` does not matter.
* "Only solutions ... $n = 2^l p$" cannot mean the starting value `n` itself: the condition
  holds for `n` whenever it holds for `g n`. For example `g 18 = 24 = 2^3 · 3`, so `n = 18`
  is a solution with `r = 2`. A direct check finds 216 solutions with `n ≤ 600`. So the
  conjecture is read up to the orbit: `(n, r)` is a solution exactly when `r = 2` and some
  iterate `g^[k] n` equals `2^l * p` with `l ≥ 1` and `p ∈ {2, 3, 5, 7, 35, 47}`. For
  `n ≤ 600` this reading agrees with a direct computation (checking `r < 20` and `k < 40`).
  The examples in the source fit it: `10 = 2 · 5` and `94 = 2 · 47`.
* `n` and `r` range over positive integers. `n = 0` is excluded because `g 0 = 0`, so it
  would trivially satisfy the condition for every `r`.
-/

namespace OMA.S_erdos_411

open Filter

/-- $g(n) = n + \phi(n)$. -/
def g (n : ℕ) : ℕ := n + Nat.totient n

theorem main :
    ∀ n r : ℕ, 1 ≤ n → 1 ≤ r →
      ((∀ᶠ k in atTop, g^[k + r] n = 2 * g^[k] n) ↔
        (r = 2 ∧ ∃ k l p : ℕ, 1 ≤ l ∧ p ∈ ({2, 3, 5, 7, 35, 47} : Finset ℕ) ∧
          g^[k] n = 2 ^ l * p)) := by
  sorry

end OMA.S_erdos_411
