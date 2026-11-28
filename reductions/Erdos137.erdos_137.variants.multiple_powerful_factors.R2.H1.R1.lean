import OMAReductions.R_Erdos137_erdos_137_variants_multiple_powerful_factors_R2

-- Reduction Erdos137.erdos_137.variants.multiple_powerful_factors.R2.H1.R1 of step Erdos137.erdos_137.variants.multiple_powerful_factors.R2.H1
-- Credit: @MBimrose

/-! # Splitting the bounded-height step into two height regimes

Hypothesis `H1` of the fixed-window reduction `...multiple_powerful_factors.R2`
quantifies over every starting point `m` with `0 < m <= n ^ D`. The two regimes
`m <= n` and `n < m <= n ^ D` behave very differently:

* For `m <= n` the window `(m, m + n]` reaches up to `2 * n`, so every prime
  `p` with `(m + n) / 2 < p <= m + n` lies inside the window and has no second
  multiple there (`2 * p > m + n`); hence any lower bound for the number of
  primes in a dyadic interval `(x / 2, x]` gives the required count. This
  regime is the one where the count comes from primes of size comparable to the
  height, and it is isolated as `H1` below.

* For `n < m <= n ^ D` the window is short compared with its height, so primes
  of size comparable to the height are no longer known to occur in it: the
  count has to come from smaller primes with a single multiple in the window, or
  from window elements carrying a prime factor exceeding the window length.
  This regime is isolated as `H2` below.

The two regimes cover the quantifier range of the parent hypothesis, so
`H1 -> H2 -> parent.H1` is immediate by taking the maximum of the two eventual
thresholds. -/

namespace OMA.R_Erdos137_erdos_137_variants_multiple_powerful_factors_R2_H1_R1

/-- Dyadic regime of the bounded-height hypothesis: the starting point is at
most the window length, so the whole window sits at height at most `2 * n`. -/
def H1 : Prop :=
  ∀ D k : ℕ, ∀ᶠ n in Filter.atTop, ∀ m : ℕ, 0 < m → m ≤ n →
    ∃ P : Finset ℕ, P.card = k ∧ ∀ p ∈ P, p.Prime ∧
      p ∣ (∏ x ∈ Finset.Ioc m (m + n), x) ∧ ¬ p ^ 2 ∣ (∏ x ∈ Finset.Ioc m (m + n), x)

/-- Tall regime of the bounded-height hypothesis: the starting point exceeds the
window length but stays below the fixed polynomial height `n ^ D`. -/
def H2 : Prop :=
  ∀ D k : ℕ, ∀ᶠ n in Filter.atTop, ∀ m : ℕ, n < m → m ≤ n ^ D →
    ∃ P : Finset ℕ, P.card = k ∧ ∀ p ∈ P, p.Prime ∧
      p ∣ (∏ x ∈ Finset.Ioc m (m + n), x) ∧ ¬ p ^ 2 ∣ (∏ x ∈ Finset.Ioc m (m + n), x)

theorem main : H1 → H2 →
    OMA.R_Erdos137_erdos_137_variants_multiple_powerful_factors_R2.H1 := by
  intro hdyadic htall D k
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hdyadic D k)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (htall D k)
  apply Filter.eventually_atTop.mpr
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn m hm hbound
  by_cases hmn : m ≤ n
  · exact hN₁ n (le_trans (le_max_left N₁ N₂) hn) m hm hmn
  · exact hN₂ n (le_trans (le_max_right N₁ N₂) hn) m (Nat.lt_of_not_le hmn) hbound

end OMA.R_Erdos137_erdos_137_variants_multiple_powerful_factors_R2_H1_R1
