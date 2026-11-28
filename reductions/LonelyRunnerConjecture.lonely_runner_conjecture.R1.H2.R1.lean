import OMAReductions.R_LonelyRunnerConjecture_lonely_runner_conjecture_R1

-- Reduction LonelyRunnerConjecture.lonely_runner_conjecture.R1.H2.R1 of step LonelyRunnerConjecture.lonely_runner_conjecture.R1.H2
-- Credit: @John-A-McMahon

namespace OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_R1_H2_R1

-- Pillar A: explicit velocity bound for a minimal counterexample, from
-- Malikiosis-Santos-Schymura 2024 (Theorem A / Corollary 3).  If a primitive
-- strictly increasing tuple of k positive integers has no lonely time for the
-- stationary runner, then every velocity is at most (k * (k + 1)) ^ (k * k).
-- This is strictly weaker than the target: it only gives a size bound.
def H1 : Prop :=
  ∀ (k : ℕ), 3 ≤ k → k ≤ 7 → ∀ (w : Fin k → ℕ),
    (∀ i : Fin k, 0 < w i) →
    StrictMono w →
    Finset.univ.gcd w = 1 →
    (¬ ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ)) →
    ∀ i : Fin k, w i ≤ (k * (k + 1)) ^ (k * k)

-- Pillar B: the finite check for bounded velocities (Rosenfeld 2025, Section 4
-- and Table 1, with the sieve of Lemma 6 / Lemma 7).  This is strictly weaker
-- than the target: the velocities are bounded by the explicit constant above.
def H2 : Prop :=
  ∀ (k : ℕ), 3 ≤ k → k ≤ 7 → ∀ (w : Fin k → ℕ),
    (∀ i : Fin k, 0 < w i) →
    StrictMono w →
    Finset.univ.gcd w = 1 →
    (∀ i : Fin k, w i ≤ (k * (k + 1)) ^ (k * k)) →
    (∃ i : Fin k, (k + 1) ∣ w i) →
    (∃ i j : Fin k, i.val + 1 = j.val ∧ j.val + 1 < k ∧ (k - 1) * w j < 2 * k * w i) →
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ)

theorem main : H1 → H2 → OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_R1.H2 := by
  intro hbound hfinite k hk3 hk7 w hwpos hwmono hwgcd hdvd hlac
  classical
  by_contra hno
  have hwbd : ∀ i : Fin k, w i ≤ (k * (k + 1)) ^ (k * k) :=
    hbound k hk3 hk7 w hwpos hwmono hwgcd hno
  exact hno (hfinite k hk3 hk7 w hwpos hwmono hwgcd hwbd hdvd hlac)

end OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_R1_H2_R1
