import FormalConjectures.ErdosProblems.«396»

-- Reduction Erdos396.erdos_396.R3 of Erdős Problem 396
-- Credit: @Salofe

/-!
# Erdős 396 through Kummer's theorem: a carry criterion and the arithmetic core

The problem asks whether for every `k` there is an `n` such that `n (n - 1) ⋯ (n - k)` divides
the central binomial coefficient `C(2n, n)`.

By Kummer's theorem the exponent of a prime `p` in `C(2n, n)` is the number of carries when `n`
is added to itself in base `p`, that is the number of `j ≥ 1` with `p ^ j ≤ 2 * (n % p ^ j)`.

* `H1` (a lemma): if for every prime `p` the total `p`-adic valuation of `n, n - 1, …, n - k` is at
  most that number of carries, then `n (n - 1) ⋯ (n - k)` divides `C(2n, n)`.
* `H2` (the open arithmetic core): for every `k` some `n > k` satisfies the carry inequality at
  every prime. In this form the problem is a statement about the base-`p` digits of `n` at the
  primes dividing `n, n - 1, …, n - k` only: a prime `p > 2k` dividing some `n - i` produces no
  carry in the last digit, so it needs a carry in a higher digit, and in particular `p ^ 2 ≤ 2n`.
-/

namespace OMA.R_Erdos396_erdos_396_R3

/-- Kummer's carry criterion for divisibility of the central binomial coefficient by a
falling factorial. -/
def H1 : Prop :=
  ∀ k n : ℕ, k < n →
    (∀ p : ℕ, p.Prime →
      ∑ i ∈ Finset.range (k + 1), padicValNat p (n - i) ≤
        ((Finset.Ico 1 (2 * n + 1)).filter fun j => p ^ j ≤ 2 * (n % p ^ j)).card) →
    Nat.descFactorial n (k + 1) ∣ Nat.centralBinom n

/-- The arithmetic core: for every `k` the carry inequality is solvable at all primes at once. -/
def H2 : Prop :=
  ∀ k : ℕ, ∃ n : ℕ, k < n ∧ ∀ p : ℕ, p.Prime →
    ∑ i ∈ Finset.range (k + 1), padicValNat p (n - i) ≤
      ((Finset.Ico 1 (2 * n + 1)).filter fun j => p ^ j ≤ 2 * (n % p ^ j)).card

theorem main : H1 → H2 → type_of% @Erdos396.erdos_396 := by
  intro h1 h2 k
  obtain ⟨n, hkn, h⟩ := h2 k
  exact ⟨n, h1 k n hkn h⟩

end OMA.R_Erdos396_erdos_396_R3
