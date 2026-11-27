import OMAReductions.R_Erdos384_erdos_384_R1

-- Reduction Erdos384.erdos_384.R1.H2.R1 of step H2 of Erdos384.erdos_384.R1
-- Credit: @JamesSlash
-- Each H becomes its own step once this file is accepted. Proving all of them closes the step.
--
-- Step H2 is Ecklund's theorem on the central range 4 ≤ k, √n ≤ k ≤ n/2. Ecklund's paper
-- [Ec69] treats this range in three different ways; together with the finitely many small k
-- this gives four independent pieces:
--   H1 (4 ≤ k < 60, hence n < 3600): a finite verification (for instance a prime p ≤ n/2 with a
--       carry in base p when adding k and n - k, by Kummer's theorem).
--   H2 (60 ≤ k, k³ < n², n ≤ k²): Ecklund's case 1 with the sieve by 2, 3 and 5: if no prime
--       p ≤ n/2 divides C(n, k), then (n/k)^k ≤ C(n, k) ≤ n^(π(n) - π(n - k)) ≤ n^(k/3).
--   H3 (60 ≤ k, n² ≤ k³, 16k ≤ n): Ecklund's case 2, through C(⌊n/2⌋, ⌊k/2⌋), which would
--       have no prime factor above k, against explicit bounds for θ and π.
--   H4 (60 ≤ k, n < 16k, 2k ≤ n): Ecklund's case 3, explicit prime-counting estimates on
--       (n - k, n] (Rosser–Schoenfeld).
-- main dispatches on k < 60, k³ < n² and 16k ≤ n.
--
-- [Ec69] E. F. Ecklund Jr., On prime divisors of the binomial coefficient,
--        Pacific J. Math. 29 (1969), 267–270.

namespace OMA.R_Erdos384_erdos_384_R1_H2_R1

/-- Small `k`: `4 ≤ k < 60` (so `n ≤ k² < 3600`). -/
def H1 : Prop :=
  ∀ n k : ℕ, 4 ≤ k → k < 60 → n ≤ k * k → 2 * k ≤ n →
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

/-- Ecklund's case 1 with the sieve by `2, 3, 5`: `60 ≤ k`, `k³ < n²`, `n ≤ k²`. -/
def H2 : Prop :=
  ∀ n k : ℕ, 60 ≤ k → k * k * k < n * n → n ≤ k * k →
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

/-- Ecklund's case 2: `60 ≤ k`, `n² ≤ k³`, `16k ≤ n`. -/
def H3 : Prop :=
  ∀ n k : ℕ, 60 ≤ k → n * n ≤ k * k * k → 16 * k ≤ n →
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

/-- Ecklund's case 3: `60 ≤ k`, `2k ≤ n < 16k`. -/
def H4 : Prop :=
  ∀ n k : ℕ, 60 ≤ k → n < 16 * k → 2 * k ≤ n →
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos384_erdos_384_R1.H2 := by
  intro ha hb hc hd n k hk hnk h2k
  by_cases h60 : k < 60
  · exact ha n k hk h60 hnk h2k
  · by_cases h3 : k * k * k < n * n
    · exact hb n k (by omega) h3 hnk
    · by_cases h16 : 16 * k ≤ n
      · exact hc n k (by omega) (Nat.not_lt.mp h3) h16
      · exact hd n k (by omega) (by omega) h2k

end OMA.R_Erdos384_erdos_384_R1_H2_R1
