import OMAReductions.R_Erdos396_erdos_396_R1

-- Reduction Erdos396.erdos_396.R1.H2.R3 of Erdos396.erdos_396.R1.H2
-- Credit: @Salofe

/-!
# Erdős 396 for `k ≥ 5`: a refined Kummer criterion, small and large primes apart

The step asks that for every `k ≥ 5` some `n` makes `n (n - 1) ⋯ (n - k)` divide the central
binomial coefficient `C(2n, n)`.

By Kummer's theorem the exponent of a prime `p` in `C(2n, n)` is the number of carries when `n`
is added to itself in base `p`, that is the number of `j ≥ 1` with `p ^ j ≤ 2 * (n % p ^ j)`.

The primes are treated in two groups. A prime `p ≤ k` may divide several of the `k + 1`
consecutive numbers `n, n - 1, …, n - k`, so the total of their `p`-adic valuations is compared
with the number of carries. A prime `p > k` divides at most one of these numbers (two of them
differ by a positive amount at most `k < p`), so only that single valuation has to be compared
with the number of carries.

* `H1` (a lemma): if `n > k` satisfies both comparisons, then `n (n - 1) ⋯ (n - k)` divides
  `C(2n, n)`.
* `H2` (the open arithmetic core): for every `k ≥ 5` some `n > k` satisfies both comparisons.
-/

namespace OMA.R_Erdos396_erdos_396_R1_H2_R3

/-- The refined carry criterion: small primes by total valuation, large primes one factor at a
time. -/
def H1 : Prop :=
  ∀ k n : ℕ, k < n →
    (∀ p : ℕ, p.Prime → p ≤ k → ∑ i ∈ Finset.range (k + 1), padicValNat p (n - i) ≤
        ((Finset.Ico 1 (2 * n + 1)).filter fun j => p ^ j ≤ 2 * (n % p ^ j)).card) →
    (∀ p : ℕ, p.Prime → k < p → ∀ i : ℕ, i ≤ k → p ∣ n - i → padicValNat p (n - i) ≤
        ((Finset.Ico 1 (2 * n + 1)).filter fun j => p ^ j ≤ 2 * (n % p ^ j)).card) →
    Nat.descFactorial n (k + 1) ∣ Nat.centralBinom n

/-- The arithmetic core: for every `k ≥ 5` both comparisons hold for some `n > k`. -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ n : ℕ, k < n ∧
    (∀ p : ℕ, p.Prime → p ≤ k → ∑ i ∈ Finset.range (k + 1), padicValNat p (n - i) ≤
        ((Finset.Ico 1 (2 * n + 1)).filter fun j => p ^ j ≤ 2 * (n % p ^ j)).card) ∧
    (∀ p : ℕ, p.Prime → k < p → ∀ i : ℕ, i ≤ k → p ∣ n - i → padicValNat p (n - i) ≤
        ((Finset.Ico 1 (2 * n + 1)).filter fun j => p ^ j ≤ 2 * (n % p ^ j)).card)

theorem main : H1 → H2 → OMA.R_Erdos396_erdos_396_R1.H2 := by
  intro h1 h2 k hk
  obtain ⟨n, hkn, hs, hl⟩ := h2 k hk
  exact ⟨n, h1 k n hkn hs hl⟩

end OMA.R_Erdos396_erdos_396_R1_H2_R3
