import Mathlib

/-!
# An explicit bound for the least prime in an arithmetic progression

Source: A. Fiori, *The Least Prime in Arithmetic an Progression*,
https://arxiv.org/abs/2404.02329 (Conjecture 9, first part; quoted in the abstract)
Credit: @SulkBash

## The problem (as the source states it)

For a modulus $n$ and $a < n$ with $\gcd(a, n) = 1$, let
$P(n, a) := \min\{p \text{ prime} \mid p \equiv a \pmod n\}$, and
$P(n) := \max_{(n,a)=1} P(n, a)$.

**Conjecture 9.** For all $n > 3$ we have $P(n) < 3\phi(n)\log(n)\log(\phi(n))$, and for all
$n > 570$ we have $P(n) > 0.5\,\phi(n)\log(n)\log(\phi(n))$.

The abstract quotes the first part ("for $n > 3$ we have a bound of
$3\phi(n)\log(n)\log(\phi(n))$"), and the paper reports a verification up to $10^8$. `main` states
that first part. The lower bound for $n > 570$ is a separate assertion and is not included.

## Formalization notes

* **Equivalent form.** Since $P(n, a)$ is a minimum, $P(n) < B$ holds iff every residue $a < n$
  coprime to $n$ has a prime $p \equiv a \pmod n$ with $p < B$. `main` states that form.
  - The prime may equal $a$ itself; for example $P(4, 3) = 3$.
* **Notation.** $\phi$ is `Nat.totient`, and $\log$ is the natural logarithm `Real.log`. With
  base-10 logarithms the bound would already fail at $n = 4$, where $P(4) = 5$.
* **Range.** For $n > 3$, $\phi(n) \ge 2$, so all logarithms are positive. The bound fails at
  $n = 3$, where $P(3) = 7 > 6 \log 3 \log 2$; this is why the source excludes it.
-/

namespace OMA.S_arxiv_2404_02329

/-- Fiori's Conjecture 9 (upper bound): for `n > 3`, every residue class `a` coprime to `n`
contains a prime `p < 3 φ(n) log(n) log(φ(n))`, i.e. `P(n) < 3 φ(n) log n log φ(n)`. -/
theorem main :
    ∀ n : ℕ, 3 < n → ∀ a : ℕ, a < n → Nat.Coprime a n →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD n] ∧
        (p : ℝ) < 3 * (n.totient : ℝ) * Real.log n * Real.log (n.totient : ℝ) := by
  sorry

end OMA.S_arxiv_2404_02329
