import Mathlib

/-!
# A Lucas congruence for Cooper's level 11 Apéry-like sequence

Source: S. Cooper, *Apéry-like sequences defined by four-term recurrence relations*,
https://arxiv.org/abs/2302.00757 (Conjecture 5.1; also quoted in the abstract)
Credit: @SulkBash

## The problem (as the source states it)

Let $T(n)$ be defined by $T(0) = 1$ and the four-term recurrence
$$(n+1)^3T(n+1) = 2(2n+1)(5n^2+5n+2)T(n) - 8n(7n^2+1)T(n-1) + 22n(2n-1)(n-1)T(n-2).$$
The single initial condition is enough to start the recurrence. The paper shows (Section 5, from
the $q$-expansions of the level 11 modular functions) that $T(n)$ is always an integer. The first
terms are $1, 4, 28, 268, 3004, 36784, 476476, \dots$

**Conjecture 5.1.** The sequence $\{T(n)\}$ satisfies a Lucas congruence for every prime $p$.
That is, for every prime $p$ and any positive integer $n$,
$$T(n) \equiv T(n_0)T(n_1)\cdots T(n_r) \pmod p,$$
where $n = n_0 + n_1 p + \cdots + n_r p^r$ is the $p$-adic expansion of $n$ in base $p$.

The paper reports checking all primes $p < 1000$ and all $n < 50000$.

## Formalization notes

* **Definition of `T`.** `T : ℕ → ℚ` follows the recurrence exactly, dividing by $(n+1)^3$ in
  `ℚ`.
  - The coefficients of $T(n-1)$ and $T(n-2)$ contain the factors $n$ and $n(n-1)$. So when
    `n - 1` or `n - 2` truncates in `ℕ`, the corresponding term is multiplied by `0`, as in the
    source's self-starting recurrence.
* **The congruence.** The base-$p$ digits $n_0, \dots, n_r$ are `Nat.digits p n`, least
  significant first and without leading zeros.
  - $T(n) \equiv \prod T(n_i) \pmod p$ is stated as: $T(n) - \prod_i T(n_i) = p z$ for some
    $z \in \mathbb{Z}$.
  - Since the $T(n)$ are integers, which the source proves, this is exactly the congruence
    modulo $p$. Stating it in `ℚ` avoids depending on that integrality theorem.
-/

namespace OMA.S_arxiv_2302_00757

/-- Cooper's level 11 sequence: `T 0 = 1` and
`(n+1)³ T(n+1) = 2(2n+1)(5n²+5n+2) T(n) - 8n(7n²+1) T(n-1) + 22n(2n-1)(n-1) T(n-2)`. -/
def T : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
    (2 * (2 * (n : ℚ) + 1) * (5 * (n : ℚ) ^ 2 + 5 * n + 2) * T n
      - 8 * (n : ℚ) * (7 * (n : ℚ) ^ 2 + 1) * T (n - 1)
      + 22 * (n : ℚ) * (2 * (n : ℚ) - 1) * ((n : ℚ) - 1) * T (n - 2)) / ((n : ℚ) + 1) ^ 3
termination_by n => n
decreasing_by all_goals omega

/-- Cooper's Conjecture 5.1: `T` satisfies the Lucas congruence
`T(n) ≡ T(n₀) T(n₁) ⋯ T(n_r) (mod p)` for every prime `p` and every positive `n`. -/
theorem main :
    ∀ p : ℕ, p.Prime → ∀ n : ℕ, 0 < n →
      ∃ z : ℤ, T n - ((Nat.digits p n).map T).prod = (p : ℚ) * z := by
  sorry

end OMA.S_arxiv_2302_00757
