import FormalConjectures.ErdosProblems.«389»

-- Reduction Erdos389.erdos_389.R1 of Erdős Problem 389
-- Credit: @JamesSlash
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 389: the large primes are exactly a smoothness condition

Write `L = n(n+1)⋯(n+k-1)`, `R = (n+k)⋯(n+2k-1)`, `N = n+2k-1` and `B = max(n-1, ⌊√N⌋)`.
For a prime `p > B` we have `p > n-1` and `p² > N`, so Legendre's formula has one term:
with `k = Qp + r` (`0 ≤ r < p`), `v_p(L) = Q + [r+n-1 ≥ p]` and
`v_p(R) = Q + ⌊(2r+n-1)/p⌋ - [r+n-1 ≥ p]`. Hence `v_p(L) ≤ v_p(R)` fails exactly when
`(n-1)/2 < p - r ≤ n-1`, i.e. exactly when `p` divides `k + s` for some `s` with `(n-1)/2 < s ≤ n-1`.
So `L ∣ R` holds if and only if
* every `k + s` with `(n-1)/2 < s ≤ n-1` is `B`-smooth, and
* `v_p(L) ≤ v_p(R)` for every prime `p ≤ B`.

* `H1` (open): for every `n ≥ 1` some `k ≥ 1` satisfies both conditions. By the equivalence above it holds
  for every `n` for which a witness `k` is known (OEIS A375071, `n ≤ 29`; e.g. `k = 207` for `n = 4`).
* `H2` (bookkeeping, provable): the two conditions imply `L ∣ R` (the computation above for `p > B`, the
  second condition for `p ≤ B`, then compare factorizations).
-/

namespace OMA.R_Erdos389_erdos_389_R1

/-- Some `k` makes the block `k + s`, `(n-1)/2 < s ≤ n-1`, smooth and satisfies the small-prime
valuation inequalities. -/
def H1 : Prop := ∀ n ≥ 1, ∃ k ≥ 1,
    (∀ s : ℕ, n - 1 < 2 * s → s ≤ n - 1 → ∀ p : ℕ, p.Prime → p ∣ k + s →
      p ≤ max (n - 1) (Nat.sqrt (n + 2 * k - 1))) ∧
    (∀ p : ℕ, p.Prime → p ≤ max (n - 1) (Nat.sqrt (n + 2 * k - 1)) →
      padicValNat p (∏ i ∈ Finset.range k, (n + i)) ≤
        padicValNat p (∏ i ∈ Finset.range k, (n + k + i)))

/-- Smoothness of the block plus the small-prime inequalities give the divisibility. -/
def H2 : Prop := ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    (∀ s : ℕ, n - 1 < 2 * s → s ≤ n - 1 → ∀ p : ℕ, p.Prime → p ∣ k + s →
      p ≤ max (n - 1) (Nat.sqrt (n + 2 * k - 1))) →
    (∀ p : ℕ, p.Prime → p ≤ max (n - 1) (Nat.sqrt (n + 2 * k - 1)) →
      padicValNat p (∏ i ∈ Finset.range k, (n + i)) ≤
        padicValNat p (∏ i ∈ Finset.range k, (n + k + i))) →
    ∏ i ∈ Finset.range k, (n + i) ∣ ∏ i ∈ Finset.range k, (n + k + i)

theorem main : H1 → H2 → type_of% @Erdos389.erdos_389 := by
  intro h1 h2 n hn
  obtain ⟨k, hk, hs, hp⟩ := h1 n hn
  exact ⟨k, hk, h2 n k hn hk hs hp⟩

end OMA.R_Erdos389_erdos_389_R1
