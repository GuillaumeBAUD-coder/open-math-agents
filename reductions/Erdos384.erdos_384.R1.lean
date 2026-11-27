import FormalConjectures.ErdosProblems.«384»

-- Reduction Erdos384.erdos_384.R1 of Erdős Problem 384
-- Credit: @JamesSlash
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Ecklund's theorem [Ec69]: if 1 < k < n - 1 and (n, k) is not (7, 3) or (7, 4), then some
-- prime p with 2p ≤ n divides C(n, k). By the symmetry C(n, k) = C(n, n - k) it suffices to
-- treat 2k ≤ n. Following the case split of Ecklund's paper, the range of k splits in three:
--   H1 (small k against n, 4 ≤ k and k² < n): Ecklund's first case. If no prime p ≤ n/2
--       divides C(n, k), then C(n, k) divides the product of the primes in (n - k, n], so
--       (n/k)^k ≤ C(n, k) ≤ n^(π(n) - π(n - k)) ≤ n^(k/2) (sieving by 2 and 3), which forces
--       n ≤ k². Elementary.
--   H2 (the central range, 4 ≤ k, √n ≤ k ≤ n/2): Ecklund's second and third cases, which use
--       explicit prime-counting estimates (Rosser–Schoenfeld) and Faulkner's lemma. This is
--       the hard core.
--   H3 (k = 2 and k = 3): direct divisibility arguments; the single exception is C(7, 3) = 35.
-- main applies the symmetry and dispatches on the three ranges.
--
-- [Ec69] E. F. Ecklund Jr., On prime divisors of the binomial coefficient,
--        Pacific J. Math. 29 (1969), 267–270.

namespace OMA.R_Erdos384_erdos_384_R1

/-- Ecklund's first case: if `4 ≤ k` and `k² < n`, then `C(n, k)` has a prime factor
`p` with `2p ≤ n`. -/
def H1 : Prop :=
  ∀ n k : ℕ, 4 ≤ k → k * k < n → ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

/-- The central range: if `4 ≤ k`, `n ≤ k²` and `2k ≤ n`, then `C(n, k)` has a prime factor
`p` with `2p ≤ n`. -/
def H2 : Prop :=
  ∀ n k : ℕ, 4 ≤ k → n ≤ k * k → 2 * k ≤ n →
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

/-- The cases `k = 2` and `k = 3` (with `2k ≤ n`), whose only exception is `C(7, 3)`. -/
def H3 : Prop :=
  ∀ n k : ℕ, 2 ≤ k → k ≤ 3 → 2 * k ≤ n → (n, k) ≠ (7, 3) →
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

theorem main : H1 → H2 → H3 → type_of% @Erdos384.erdos_384 := by
  intro h1 h2 h3 n k hk hkn h₃ h₄
  have key : ∀ k' : ℕ, 1 < k' → 2 * k' ≤ n → (n, k') ≠ (7, 3) →
      ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k' ∧ 2 * p ≤ n := by
    intro k' hk' h2k' h7
    by_cases hk3 : k' ≤ 3
    · exact h3 n k' hk' hk3 h2k' h7
    · by_cases hsq : k' * k' < n
      · exact h1 n k' (by omega) hsq
      · exact h2 n k' (by omega) (by omega) h2k'
  by_cases hkk : 2 * k ≤ n
  · exact key k hk hkk h₃
  · have h7 : (n, n - k) ≠ (7, 3) := by
      intro h
      apply h₄
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨h.1, by omega⟩
    have := key (n - k) (by omega) (by omega) h7
    rwa [Nat.choose_symm (by omega)] at this

end OMA.R_Erdos384_erdos_384_R1
